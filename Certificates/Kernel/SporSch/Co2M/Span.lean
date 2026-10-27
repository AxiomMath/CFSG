
module

public import Certificates.Kernel.SporSch.Co2M.Seeds
public import CFSG.Certificates.Kernel.SporSch.Co2LESound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatInj CFSG.KS.Co2LE CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Cert

@[expose] def BL : List (List ℕ) :=
  [[2, 4, 6, 9, 10, 13, 14, 18, 23, 28, 41], [0, 1, 6, 9, 10, 11, 12, 18],
    [0, 1, 2, 3, 4, 5, 6, 7, 9, 12, 41], [0, 3, 4, 6, 8, 10, 11, 12, 13, 14, 15, 17, 18],
    [0, 8, 12, 14, 15, 18, 41], [1, 6, 7, 9, 11, 15, 17, 18, 23, 41, 61],
    [3, 4, 5, 6, 7, 8, 9, 14, 17, 18, 23], [0, 4, 5, 9, 13, 14, 15, 17, 18, 23, 41, 61],
    [0, 2, 3, 4, 7, 10, 13, 14, 17, 41], [1, 2, 3, 6, 8, 9, 10, 11, 13, 18, 28, 61],
    [0, 2, 7, 9, 13, 14, 15, 61], [0, 1, 2, 3, 6, 7, 10, 11, 17, 28, 41],
    [0, 3, 5, 8, 12, 13, 14, 17, 61], [2, 4, 6, 8, 9, 11, 12, 17, 23, 41],
    [4, 6, 11, 12, 13, 14, 15, 17, 18, 23, 28, 41, 61], [1, 3, 8, 10, 11, 12, 13, 15, 17, 18, 23, 61],
    [1, 2, 4, 7, 8, 9, 10, 11, 18, 61], [0, 1, 3, 8, 9, 12, 13, 15, 28],
    [0, 2, 4, 7, 8, 9, 17, 23, 28, 61], [2, 3, 5, 6, 9, 10, 11, 12, 18],
    [3, 4, 8, 10, 11, 12, 13, 14, 15, 17, 18, 41], [0, 3, 6, 10, 11, 12, 13, 15, 17, 28]]

@[expose] noncomputable def xorK (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun i _ acc => Nat.xor (VG (PV 0) i) acc) l

@[expose] noncomputable def ltK (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun i _ acc => bAnd(Nat.blt i (nat_lit 2300), acc)) l

theorem span_ok : allN 22 (fun r => bAnd(ltK (BL.getD r []),
    Nat.beq (xorK (BL.getD r [])) (Nat.shiftLeft (nat_lit 1) r))) = true := by
  decide +kernel

theorem xorK_eq : ∀ l : List ℕ, ltK l = true →
    (∀ i ∈ l, i < co2PackedVecs.size) ∧ xorAt co2PackedVecs l = xorK l
  | [], _ => ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩
  | i :: l, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (ltK l) (Nat.blt i 2300) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    have hi : i < 2300 := by rwa [Nat.blt_eq] at h1
    obtain ⟨ih1, ih2⟩ := xorK_eq l h2
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · rw [V_size]; exact hi
      · exact ih1 j hj
    · rw [xorAt, List.foldr_cons, ← xorAt, ih2, V_get hi]
      rfl

theorem spans : Spans 22 co2PackedVecs := by
  intro r hr
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec span_ok r hr)
  obtain ⟨hl, hx⟩ := xorK_eq _ h1
  refine ⟨_, hl, ?_⟩
  rw [hx, Nat.eq_of_beq_eq_true h2]
  change 1 <<< r = 2 ^ r
  rw [Nat.shiftLeft_eq, one_mul]

theorem vok : VOK co2PackedVecs (PV 0) := ⟨good, V_size, fun _ hi => V_get hi, spans⟩

end CertificateChecks.KernelSporSch.Co2M

end
