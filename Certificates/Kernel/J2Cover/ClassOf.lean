
module

public import CFSG.Certificates.Kernel.J2CoverSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.SiftRSound

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.Kernel

@[expose] def RepFacts (nb BP : Nat) (LR TRI : Nat → Nat) (R : Nat) : Prop :=
  invEqK 315 9 (mask 9) (315 * 9) R (pinvS 315 9 (mask 9) R) = true ∧
    canonK 315 9 (mask 9) (315 * 9) R = true ∧ ord4K 315 9 R = true ∧
    Nat.beq (Nat.shiftRight R (315 * 9)) 0 = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) LR TRI BP nb 0 R = true

theorem classCheck_of {S : Array (Array Nat)} {k : Nat} {base : Array Nat}
    {reps : List (Array Nat)} {sizes : List Nat} {kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    (hb : Binds 315 9 PS kS nb BP S base)
    (hp : allN kS (fun j => permOK 315 9 (mask 9) (315 * 9) (PS j) (PSI j)) = true)
    (hl : LevelsOK 315 9 PS PSI LR TR TRI kS nb BP) (hk : k ≤ kS)
    {GP GIP CI E P L K Ss SI : Nat → Nat} {CS OFF : List Nat} {N : Nat}
    (hGP : ∀ l < k, GP l = PS l ∧ GIP l = PSI l)
    (hgc : ∀ l < k, canonK 315 9 (mask 9) (315 * 9) (GP l) = true ∧
      canonK 315 9 (mask 9) (315 * 9) (GIP l) = true)
    (hinv : ∀ l < k, pcomp 315 9 (mask 9) (GP l) (GIP l) = pidn 315 9)
    (hreps : reps = (List.range CS.length).map fun i => unpack 315 9 (E (lget OFF i)))
    (hoff : offOK CS OFF N = true) (hpos : allL (fun c => Nat.blt 0 c) CS = true)
    (hcnt : prodCnt 315 9 nb LR TR (ord4K 315 9) = N)
    (h : ∀ j < N, repK 315 9 GP GIP k CS OFF CI E P L K Ss SI N 4000 j = true)
    (hsz : CS = sizes)
    (hrep : ∀ i < CS.length, RepFacts nb BP LR TRI (E (lget OFF i))) :
    classCheck S k base reps sizes = true := by
  have hg : (genTbls S k).size = k ∧ (genInvTbls S k).size = k ∧ ∀ l < k,
      (genTbls S k)[l]! = arrTable 315 (unpack 315 9 (GP l)) ∧
        (genInvTbls S k)[l]! = arrTable 315 (unpack 315 9 (GIP l)) := by
    refine ⟨by simp [genTbls], by simp [genInvTbls], fun l hl => ⟨?_, ?_⟩⟩
    · rw [genTbls, getElem!_pos _ l (by simp [hl])]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [hb.2.2.2.2.1 l (by omega), (hGP l hl).1]
    · rw [genInvTbls, getElem!_pos _ l (by simp [hl])]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [hb.2.2.2.2.1 l (by omega), (invEqK_sound (allN_spec hp l (by omega))).1, (hGP l hl).2]
  have hreps' : reps.map (arrTable 315) =
      (List.range CS.length).map fun i => arrTable 315 (unpack 315 9 (E (lget OFF i))) := by
    rw [hreps, List.map_map, Function.comp_def]
  have hX : (fourTables S base).length = N := by
    unfold fourTables
    rw [prodCnt_sound hb hp hl (fun X hX => ord4_unpack hX)]
    exact hcnt
  have h1 := repsOK_sound hg hgc hreps' hoff hpos hX h
  have h2 := repSizes_sound hg hgc hreps' hoff hpos h
  have h3 := closedOK_sound hg hgc hinv hoff hpos h rfl
  unfold classCheck
  rw [h1, h2, ← hsz, beq_self_eq_true, Bool.true_and, Bool.true_and, List.all_eq_true]
  intro r hr
  rw [hreps] at hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
  have hi' := List.mem_range.1 hi
  obtain ⟨hinvR, hcan, hord, hz, hs⟩ := hrep i hi'
  obtain ⟨e1, e2⟩ := invEqK_sound hinvR
  unfold closureEntries
  rw [e1, e2, ord4_unpack hcan, hord,
    siftK_soundR hb hp hl rfl (Nat.eq_of_beq_eq_true hz) (range_of_canonK hcan) hs,
    h3 i hi']
  rfl

end CertificateChecks.KernelJ2Cover

end
