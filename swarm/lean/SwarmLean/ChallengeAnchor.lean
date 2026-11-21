/-! A workaround for the kernel replay of an export (Lean 4.35's `Kernel.Environment.replay`, which `leanchecker
--from-export` and so `lake comparator` run): it adds each constant after the constants it names, in the order of
their name hashes, and a string literal names none, so a theorem that decides a string equality and replays before
`String.ofList` fails. This theorem's name has a hash below every other name in the export, so it replays first and
brings `String.ofList` and `Char.ofNat` in; when the kernel rejects, `challenge.sh` prints which constant replayed
first. -/

theorem SwarmLean.strLit2953880 : String.ofList [Char.ofNat 97] = "a" := rfl
