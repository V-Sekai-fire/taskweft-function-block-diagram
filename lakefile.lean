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
    `TaskweftFbdCompiler.Sgd,
    `TaskweftFbdCompiler.Dsl,
    `TaskweftFbdCompiler.Xml,
    `TaskweftFbdCompiler.Lift,
    `TaskweftFbdCompiler.Elf
  ]

@[default_target]
lean_exe taskweft_fbd_compiler where
  root := `Main
