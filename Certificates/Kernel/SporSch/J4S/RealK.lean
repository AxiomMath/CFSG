module

public import CFSG.Sporadic.Schreier.J4SRealData
public import Certificates.Kernel.SporSch.J4S.Gen
public import Certificates.Kernel.J4Q.Mat
public import CFSG.Certificates.Kernel.SporSch.J4SBigSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.J4.PrimSpec
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Sporadic.Schreier.J4SRealData
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 400000

#kss_rows CertificateChecks.KernelSporSch.J4SR CFSG.Sporadic.J4Schreier.spanRows
#kss_rows CertificateChecks.KernelSporSch.J4SI CFSG.Sporadic.J4Schreier.spanInvRows

namespace CertificateChecks.KernelSporSch.J4Real

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch

theorem b3 : Nat.beq (mulJ c rm B (mulJ c rm B B)) Bi = true := by quickRfl

theorem rows : allN 112 (fun i => Nat.beq (rowJ rm J4SR i) (wvK rm one A Bi B spanWords[i]! rootBits)) =
    true := by quickRfl

theorem rcanon : canonJ pad J4SR = true := by quickRfl

theorem pinv : packNK spanInvRows.toList J4SI = true := by quickRfl

theorem inv : Nat.beq (mulJ c rm J4SI J4SR) one = true := by quickRfl

theorem rootLt : rootBits < 2 ^ 112 := by decide

theorem letters : ∀ i < 112, ∀ l ∈ spanWords[i]!, l = 1 ∨ l = 2 := by decide +kernel

theorem sizes : ∀ T T' : Finset (Fin 7), T.Nonempty → T'.Nonempty → Disjoint T T' →
    (∑ i ∈ T, CFSG.Sporadic.J4.subSizesF i) ∣ 501397585920 →
    (∑ i ∈ T', CFSG.Sporadic.J4.subSizesF i) ∣ 501397585920 →
    (∑ i ∈ T, CFSG.Sporadic.J4.subSizesF i) ≠ ∑ i ∈ T', CFSG.Sporadic.J4.subSizesF i := by
  decide +kernel

theorem hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6 := CertificateChecks.KernelJ4Q.hK

theorem seed1 : CFSG.Blueprint.NativeSporadic.J4Seed1 = String.ofList LA := by
  rw [← CFSG.KD.J4Q.LA_eq]
  rfl

theorem seed2 : CFSG.Blueprint.NativeSporadic.J4Seed2 = String.ofList LB := by
  rw [← CFSG.KD.J4Q.LB_eq]
  rfl

theorem decA : decOK A LA = true := by quickRfl

theorem decB : decOK B LB = true := by quickRfl

theorem decs : decOK A LA = true ∧ decOK B LB = true := ⟨decA, decB⟩

theorem hA : WfN (O.decode CFSG.Blueprint.NativeSporadic.J4Seed1) ∧
    encN (O.decode CFSG.Blueprint.NativeSporadic.J4Seed1) = A := by
  rw [seed1]
  exact decode_enc hK decs.1

theorem hB : WfN (O.decode CFSG.Blueprint.NativeSporadic.J4Seed2) ∧
    encN (O.decode CFSG.Blueprint.NativeSporadic.J4Seed2) = B := by
  rw [seed2]
  exact decode_enc hK decs.2

theorem hB3 : WfN Bn.2 ∧ encN Bn.2 = Bi := by
  have e : Bn.2 = O.mul (O.decode CFSG.Blueprint.NativeSporadic.J4Seed2)
      (O.mul (O.decode CFSG.Blueprint.NativeSporadic.J4Seed2)
        (O.decode CFSG.Blueprint.NativeSporadic.J4Seed2)) := pow3_eq _
  have m1 := mul_enc hK hB.1 hB.1
  have m2 := mul_enc hK hB.1 m1.1
  rw [e]
  refine ⟨m2.1, ?_⟩
  rw [m2.2, m1.2, hB.2]
  exact Nat.eq_of_beq_eq_true b3

theorem letter {l : Int} (hl : l = 1 ∨ l = 2) :
    WfN (letterP An Bn l).2 ∧ encN (letterP An Bn l).2 = letK2 one A Bi B l := by
  rcases hl with rfl | rfl
  · exact hA
  · exact hB3

theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem wv : ∀ w : List Int, (∀ l ∈ w, l = 1 ∨ l = 2) → WfN (wordP An Bn w).2 ∧
    ∀ v < 2 ^ 112, vecMulN 112 (wordP An Bn w).2 v = wvK rm one A Bi B w v
  | [], _ => ⟨(id_enc hK).1, fun _ hv => id_vec hv⟩
  | l :: w, h => by
    have ih := wv w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hL := letter (h l List.mem_cons_self)
    have e : (wordP An Bn (l :: w)).2 = O.mul (wordP An Bn w).2 (letterP An Bn l).2 := rfl
    rw [e]
    refine ⟨(mul_enc hK ih.1 hL.1).1, fun v hv => ?_⟩
    rw [vec_mul ih.1 hL.1, ih.2 v hv, vec_enc hK hL.1, hL.2]
    exact (strictN_eq (wvK rm one A Bi B w v) (fun u => vecJ rm u (letK2 one A Bi B l))).symm

theorem facts : (mulRows 112 spanInvRows spanRows = idRows 112)
    ∧ (∀ T T' : Finset (Fin 7), T.Nonempty → T'.Nonempty → Disjoint T T' →
      (∑ i ∈ T, CFSG.Sporadic.J4.subSizesF i) ∣ 501397585920 →
      (∑ i ∈ T', CFSG.Sporadic.J4.subSizesF i) ∣ 501397585920 →
      (∑ i ∈ T, CFSG.Sporadic.J4.subSizesF i) ≠ ∑ i ∈ T', CFSG.Sporadic.J4.subSizesF i) := by
  refine ⟨?_, sizes⟩
  have hr : WfN spanRows ∧ encN spanRows = J4SR := by
    refine ofFn_enc hK (fun i => ?_) rcanon (fun i => ?_)
    · rw [(wv _ (letters i.val i.isLt)).2 _ rootLt, ← Nat.eq_of_beq_eq_true (allN_spec rows i i.isLt)]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    · rw [(wv _ (letters i.val i.isLt)).2 _ rootLt]
      exact Nat.eq_of_beq_eq_true (allN_spec rows i i.isLt)
  have hi := pack_enc pinv
  have hm := mulRows_enc hK hi.1 hr.1
  apply enc_inj hm.1 (id_enc hK).1
  rw [hm.2, hi.2, hr.2, (id_enc hK).2]
  exact Nat.eq_of_beq_eq_true inv

end CertificateChecks.KernelSporSch.J4Real

end
