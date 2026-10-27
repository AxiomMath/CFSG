module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Certificates.Kernel.SporSch.ChainClsSound
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Ru.RowsGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound

public section

namespace CFSG.KS.SporSch.ChainClsG

open CFSG.KS.SporSch.MOCG

meta def commCounts (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (gs : Array (Array Nat))
    (L : Nat) : Array Nat :=
  let E := prods (levelsOf n S base) 0 (idA n)
  let N := E.size
  let NB := (N + L - 1) / L
  let ok := E.map fun x => gs.all fun g => comp x g == comp g x
  (Array.range NB).map fun s => ((List.range L).filter fun l => s * L + l < N && ok[s * L + l]!).length

meta def chainCls (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (ng : Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let E := prods (levelsOf n S base) 0 (idA n)
  let N := E.size
  let idx : Std.HashMap (Array Nat) Nat := (List.range N).foldl (fun m j => m.insert E[j]! j) {}
  let gens := (List.range ng).toArray.map fun g => S[g]!
  let gi := gens.map invA
  let cjOf := fun (j g : Nat) => idx.getD (comp gens[g]! (comp E[j]! gi[g]!)) 0
  let mut lab : Array Nat := Array.replicate N N
  let mut reps : Array Nat := #[]
  let mut sizes : Array Nat := #[]
  for i in [0:N] do
    let j := N - 1 - i
    if lab[j]! == N then
      let l := reps.size
      reps := reps.push j
      lab := lab.set! j l
      let mut queue : Array Nat := #[j]
      let mut h := 0
      while h < queue.size do
        let y := queue[h]!
        for g in [0:ng] do
          let t := cjOf y g
          if lab[t]! == N then
            lab := lab.set! t l
            queue := queue.push t
        h := h + 1
      sizes := sizes.push queue.size
  let cj := (Array.range (ng * N)).map fun i => cjOf (i / ng) (i % ng)
  return (lab, cj, reps, sizes, sizes.map fun s => N / s)

meta def singles (a : Array Nat) : Array (Array Nat) := a.map fun v => #[v]

meta def chainLabs (lab : Array Nat) (L : Nat) : Array (Array Nat) :=
  let N := lab.size
  singles ((Array.range ((N + L - 1) / L * L)).map fun j => if j < N then lab[j]! else 0)

end CFSG.KS.SporSch.ChainClsG

end
