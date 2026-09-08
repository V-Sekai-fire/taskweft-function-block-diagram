import Lake
open Lake DSL

package «taskweft-fbd-compiler» where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib TaskweftFbdCompiler where
  roots := #[
    `TaskweftFbdCompiler,
    `TaskweftFbdCompiler.Parser,
    `TaskweftFbdCompiler.Semantics,
    `TaskweftFbdCompiler.Riscv,
    `TaskweftFbdCompiler.Sigs,
    `TaskweftFbdCompiler.Sgd,
    `TaskweftFbdCompiler.Dsl,
    `TaskweftFbdCompiler.Xml,
    `TaskweftFbdCompiler.Lift,
    `TaskweftFbdCompiler.Netlist,
    `TaskweftFbdCompiler.Scan,
    `TaskweftFbdCompiler.Gen,
    `TaskweftFbdCompiler.Elf
  ]

@[default_target]
lean_exe taskweft_fbd_compiler where
  root := `Main
