/-
RFD 2153 stage 1: write a RISC-V ELF64 with the sections Godot
Sandbox's loader requires (`.text`, `.symtab`, `.strtab`,
`.shstrtab`, plus SHN_UNDEF). Emitted verbatim from Lean, no
external assembler or linker.

The ELF exports one function `_start` at the .text entry address so
`sandbox_functions.cpp`'s `get_program_info_from_binary` walks the
symtab and finds a callable entry point.

SPDX-License-Identifier: MIT OR Apache-2.0
-/
import TaskweftFbdCompiler

namespace TaskweftFbdCompiler.Elf

/-! Little-endian byte encoders. -/

def u16le (n : UInt16) : ByteArray :=
  ByteArray.mk #[
    (n &&& 0xff).toUInt8,
    ((n >>> 8) &&& 0xff).toUInt8
  ]

def u32le (n : UInt32) : ByteArray :=
  ByteArray.mk #[
    (n &&& 0xff).toUInt8,
    ((n >>> 8) &&& 0xff).toUInt8,
    ((n >>> 16) &&& 0xff).toUInt8,
    ((n >>> 24) &&& 0xff).toUInt8
  ]

def u64le (n : UInt64) : ByteArray :=
  let low  : UInt32 := (n &&& 0xffffffff).toUInt32
  let high : UInt32 := ((n >>> 32) &&& 0xffffffff).toUInt32
  u32le low ++ u32le high

/-- ELF64 identification. -/
def elfIdent : ByteArray :=
  ByteArray.mk #[
    0x7f, 0x45, 0x4c, 0x46, 0x02, 0x01, 0x01, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
  ]

/-- `_start`: `li a7, 93; li a0, 42; ecall` — the same three
    instructions ladder stage 0 produced. libriscv treats
    `ecall #93` (Linux SYS_exit) as a clean guest termination. -/
def helloTextBytes : ByteArray :=
  u32le 0x05d00893 ++
  u32le 0x02a00513 ++
  u32le 0x00000073

/-- Pad a byte array to a multiple of `align` with zero bytes. -/
def padTo (b : ByteArray) (align : Nat) : ByteArray :=
  let rem := b.size % align
  if rem = 0 then b else b ++ ByteArray.mk (Array.replicate (align - rem) 0)

/-- One ELF64 section header entry (64 bytes). -/
structure Shdr where
  name      : UInt32       -- offset into .shstrtab
  type      : UInt32
  flags     : UInt64
  addr      : UInt64
  offset    : UInt64
  size      : UInt64
  link      : UInt32 := 0
  info      : UInt32 := 0
  addralign : UInt64 := 1
  entsize   : UInt64 := 0

def encodeShdr (s : Shdr) : ByteArray :=
  u32le s.name ++ u32le s.type ++
  u64le s.flags ++ u64le s.addr ++
  u64le s.offset ++ u64le s.size ++
  u32le s.link ++ u32le s.info ++
  u64le s.addralign ++ u64le s.entsize

/-- Assemble a minimum RISC-V ELF64 with section headers Godot
    Sandbox's loader accepts. The loaded segment covers the ELF
    header + program header + `.text`; the section tables sit in
    the file but not in the loaded image. -/
def buildElf (text : ByteArray) : ByteArray := Id.run do
  let ehdrSize   : Nat := 64
  let phdrSize   : Nat := 56
  let baseAddr   : UInt64 := 0x10000

  -- Layout offsets. .text sits right after the phdr; sections after.
  let textOffset : Nat := ehdrSize + phdrSize          -- 120
  let textSize   : Nat := text.size                    -- 12
  let textAddr   : UInt64 := baseAddr + textOffset.toUInt64

  -- .symtab: two 24-byte entries (SHN_UNDEF, _start).
  let symEntry : ByteArray :=
    u32le 0 ++ ByteArray.mk #[0x00, 0x00] ++ u16le 0 ++ u64le 0 ++ u64le 0
  let startSym : ByteArray :=
    u32le 1 ++                    -- st_name = 1 (offset of "_start" in .strtab)
    ByteArray.mk #[0x12, 0x00] ++ -- st_info=STB_GLOBAL|STT_FUNC, st_other=0
    u16le 1 ++                    -- st_shndx = 1 (.text)
    u64le textAddr ++             -- st_value
    u64le textSize.toUInt64       -- st_size
  let symtab := symEntry ++ startSym
  let symtabOffset : Nat := textOffset + textSize
  let symtabSize   : Nat := symtab.size

  -- .strtab: "\0_start\0"
  let strtab : ByteArray :=
    ByteArray.mk #[0x00] ++ "_start".toUTF8 ++ ByteArray.mk #[0x00]
  let strtabOffset : Nat := symtabOffset + symtabSize
  let strtabSize   : Nat := strtab.size

  -- .shstrtab: "\0.text\0.symtab\0.strtab\0.shstrtab\0"
  let shstrtab : ByteArray :=
    ByteArray.mk #[0x00] ++
    ".text".toUTF8 ++ ByteArray.mk #[0x00] ++
    ".symtab".toUTF8 ++ ByteArray.mk #[0x00] ++
    ".strtab".toUTF8 ++ ByteArray.mk #[0x00] ++
    ".shstrtab".toUTF8 ++ ByteArray.mk #[0x00]
  let shstrtabOffset : Nat := strtabOffset + strtabSize
  let shstrtabSize   : Nat := shstrtab.size

  -- Section header table, 8-byte aligned.
  let preShoff : Nat := shstrtabOffset + shstrtabSize
  let shoff    : Nat := preShoff + ((8 - preShoff % 8) % 8)
  let shpad    : ByteArray := ByteArray.mk (Array.replicate (shoff - preShoff) 0)

  -- Name offsets into .shstrtab:  1=".text", 7=".symtab", 15=".strtab", 23=".shstrtab"
  let sh0  : Shdr := { name := 0, type := 0, flags := 0, addr := 0, offset := 0, size := 0 }
  let sh1  : Shdr := { name := 1, type := 1 /-PROGBITS-/, flags := 6 /-A|X-/,
                       addr := textAddr, offset := textOffset.toUInt64,
                       size := textSize.toUInt64, addralign := 4 }
  let sh2  : Shdr := { name := 7, type := 2 /-SYMTAB-/, flags := 0,
                       addr := 0, offset := symtabOffset.toUInt64,
                       size := symtabSize.toUInt64,
                       link := 3 /-.strtab index-/, info := 1 /-first global-/,
                       addralign := 8, entsize := 24 }
  let sh3  : Shdr := { name := 15, type := 3 /-STRTAB-/, flags := 0,
                       addr := 0, offset := strtabOffset.toUInt64,
                       size := strtabSize.toUInt64, addralign := 1 }
  let sh4  : Shdr := { name := 23, type := 3 /-STRTAB-/, flags := 0,
                       addr := 0, offset := shstrtabOffset.toUInt64,
                       size := shstrtabSize.toUInt64, addralign := 1 }
  let shtable :=
    encodeShdr sh0 ++ encodeShdr sh1 ++ encodeShdr sh2 ++
    encodeShdr sh3 ++ encodeShdr sh4

  -- The loaded segment covers Ehdr + Phdr + .text.
  let loadedSize : UInt64 := (ehdrSize + phdrSize + textSize).toUInt64

  let ehdr :=
    elfIdent ++
    u16le 0x0002 ++                     -- ET_EXEC
    u16le 0x00f3 ++                     -- EM_RISCV
    u32le 0x00000001 ++                 -- e_version
    u64le textAddr ++                   -- e_entry
    u64le ehdrSize.toUInt64 ++          -- e_phoff
    u64le shoff.toUInt64 ++             -- e_shoff
    u32le 0x00000005 ++                 -- e_flags: RVC + double-float ABI
    u16le 0x0040 ++                     -- e_ehsize (64)
    u16le 0x0038 ++                     -- e_phentsize (56)
    u16le 0x0001 ++                     -- e_phnum
    u16le 0x0040 ++                     -- e_shentsize (64)
    u16le 0x0005 ++                     -- e_shnum (5)
    u16le 0x0004                        -- e_shstrndx (4)

  let phdr :=
    u32le 0x00000001 ++                 -- PT_LOAD
    u32le 0x00000005 ++                 -- PF_R | PF_X
    u64le 0 ++                          -- p_offset
    u64le baseAddr ++                   -- p_vaddr
    u64le baseAddr ++                   -- p_paddr
    u64le loadedSize ++                 -- p_filesz
    u64le loadedSize ++                 -- p_memsz
    u64le 0x1000                        -- p_align

  return ehdr ++ phdr ++ text ++ symtab ++ strtab ++ shstrtab ++ shpad ++ shtable

def helloElf : ByteArray :=
  buildElf helloTextBytes

end TaskweftFbdCompiler.Elf
