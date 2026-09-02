# `sigs/` — target surface areas, laddered

One file per external surface the FBD compiler (RFD 2154 / 2148 / 2155)
emits into. Same convention as `2-contract/bus/iceoryx2.sigs`: one
declaration per line, `#` for comments, feeds a code generator that
produces the dispatch stubs each emitter links against.

Each file states its **rung** in its own header. Rungs are cumulative
subsets of one surface; a higher rung is a superset of a lower one.

- **Rung 0** — minimum useful for the smoke-test emitter. Just enough
  to walk a hand-authored FBD network end to end on the target.
- **Rung 1** — the subset `Taskweft.OpenPLC.PLCopen.emit/1` produces
  today (SR_L / AND / OR / NOT / MOVE / TON) reaches on the target.
  What the RFD 2154 differential covers.
- **Rung 2** — the standard block library the parser accepts.
  Deferred until the emitter body lands.

Files here today:

| file                             | rung | source                                                                       |
| -------------------------------- | ---- | ---------------------------------------------------------------------------- |
| `godot_sandbox_syscalls.sigs`    | full | libriscv/godot-sandbox `src/syscalls.h` (MIT)                                |
| `vrchat_udon_asm.sigs`           | full | vrchat-community/UdonSharp `AssemblyInstruction.cs` + `AssemblyModule.cs` (MIT) |
| `godot_engine_single.sigs`       | 0 index | **not** the source of truth — Sandbox's `generate_api("cpp",...)` is; run `mix godot.dump_api` |
| `godot_engine_double.sigs`       | 0 index | same, double-precision `real_t` sibling                                       |
| `udon_extern.sigs`               | 0    | vrchat-community/UdonSharp extern resolver + UdonManager runtime (MIT)        |
| `gltf_interactivity.sigs`        | 0    | KhronosGroup/glTF `extensions/2.0/Khronos/KHR_interactivity` (Khronos)        |
| `resonite_protoflux.sigs`        | 0    | Resonite official reference: `wiki.resonite.com` ProtoFlux node list (CC-BY) |
| `threejs.sigs`                   | 0    | mrdoob/three.js `docs/api/en/` (MIT)                                          |
| `blender_bpy.sigs`               | 0    | blender.org bpy API reference r4.2 LTS (GPL-2.0)                              |
| `openusd.sigs`                   | 0    | PixarAnimationStudios/OpenUSD `pxr/usd/{sdf,usd,usdShade}` public API (TOST-Apache-2.0) |
| `mujoco.sigs`                    | 0    | google-deepmind/mujoco MJCF XML schema + Python bindings (Apache-2.0)         |
| `mitsuba3.sigs`                  | 0    | mitsuba-renderer/mitsuba3 scene XML + Python API (BSD-3)                      |

## Two roles of a `.sigs` here

Some rows above (both Udon files, the sandbox syscalls) are the
**source of truth** — nothing upstream generates them, so this repo
maintains them by hand from the upstream sources they cite. Others
(both godot engine files today) are **indices** — the upstream ships
its own stub generator, and the `.sigs` exists only to give a reader
the rung-0 subset and to seed the anti-entropy check that compares
the curated list against what the generator actually emitted.

The rule is stated per file in its own header. A future anti-entropy
gate refuses a `.sigs` marked "not source of truth" whose entries do
not appear in the corresponding generated header, and refuses a
generator run whose header omits a rung-0 entry the `.sigs` names.

**Trademark note.** These are interop surfaces; the platform each file
targets is named because the file has no meaning without the name.
Same pattern as the two full-surface files above. No marketing copy.
