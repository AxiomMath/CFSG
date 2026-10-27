module

public import Certificates.Kernel.SporSch.J1.Chain
public import CFSG.Certificates.Kernel.Spor.PresCard
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Pres CFSG.Sporadic.Schreier
open CFSG.Monster.B.Mathieu

theorem bindsOK : allN 4 (fun k =>
    bindListK 3080 12 (J1C.S k) (j1Chain.strongGenerators.getD k [])) = true := by
  quickRfl

theorem genOK : allN 2 (fun k =>
    bindListK 3080 12 (J1C.S k) (j1Chain.generators.getD k [])) = true := by
  quickRfl

theorem perm : allN 4 (fun j => permOK 3080 12 (mask 12) (3080 * 12) (J1C.S j) (J1C.SI j)) =
    true := by
  quickRfl

theorem canonOK : allN 4 (fun j => bAnd(canonK 3080 12 (mask 12) (3080 * 12) (J1C.S j),
    canonK 3080 12 (mask 12) (3080 * 12) (J1C.SI j))) = true := by
  quickRfl

theorem idOK : bAnd(canonK 3080 12 (mask 12) (3080 * 12) (pidn 3080 12), idK 3080 12 (mask 12)) =
    true := by
  quickRfl

theorem baseOK : allN 3 (fun t => Nat.beq j1Chain.baseArr[t]! (pg 12 (mask 12) J1C.BP t)) =
    true := by
  quickRfl

@[expose] noncomputable def G (i : Nat) : Nat := nIf(Nat.beq i 0, J1C.S 0, J1C.S 1)

@[expose] noncomputable def GI (i : Nat) : Nat := nIf(Nat.beq i 0, J1C.SI 0, J1C.SI 1)

@[expose] def abW : List (Nat × Bool) := [(0, true), (1, true)]

@[expose] def repW : List (Nat × Bool) := [(0, true), (1, true), (0, true), (1, false)]

@[expose] def fifthW : List (Nat × Bool) := abW ++ repW ++ repW ++ repW

@[expose] def squareW : List (Nat × Bool) :=
  abW ++ repW ++ repW ++ repW ++ repW ++ repW ++ repW ++
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)]

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true)],
    abW ++ abW ++ abW ++ abW ++ abW ++ abW ++ abW,
    fifthW ++ fifthW ++ fifthW ++ fifthW ++ fifthW, squareW ++ squareW]

theorem rel0 : Nat.beq (wordPK 3080 12 G GI (rels.getD 0 [])) (pidn 3080 12) = true := by
  quickRfl

theorem rel1 : Nat.beq (wordPK 3080 12 G GI (rels.getD 1 [])) (pidn 3080 12) = true := by
  quickRfl

theorem rel2 : Nat.beq (wordPK 3080 12 G GI (rels.getD 2 [])) (pidn 3080 12) = true := by
  quickRfl

theorem rel3 : Nat.beq (wordPK 3080 12 G GI (rels.getD 3 [])) (pidn 3080 12) = true := by
  quickRfl

theorem rel4 : Nat.beq (wordPK 3080 12 G GI (rels.getD 4 [])) (pidn 3080 12) = true := by
  quickRfl

theorem rels_list :
    rels = [rels.getD 0 [], rels.getD 1 [], rels.getD 2 [], rels.getD 3 [], rels.getD 4 []] :=
  rfl

theorem relsOK : ∀ v ∈ rels, Nat.beq (wordPK 3080 12 G GI v) (pidn 3080 12) = true := by
  rw [rels_list]
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  exacts [rel0, rel1, rel2, rel3, rel4]

end CertificateChecks.KernelSporSch.J1

end
