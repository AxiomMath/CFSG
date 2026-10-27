module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoTableTTransport
import CFSG.Certificates.Kernel.E6TT.CoverSound
import CFSG.Certificates.Kernel.E6TT.RowA2Sound
import Certificates.Kernel.E6TT.EnumChecks
import Certificates.Kernel.E6TT.CoverCheck
import Certificates.Kernel.E6TT.WeylChecks
import Certificates.Kernel.E6TT.RowChecks
import Certificates.Kernel.E6TT.RowChecksA2

namespace CertificateChecks.KernelE6TT

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.KC.E6TT
open Certificates.Data.E6TableT (Vec roots reps classes)
open CFSG.StandardType.TablePThreeKG (E6Admissible E6TableTTwoAt E6TableTTwoStmt repZ bList
  e6TableTTwoStmt_iff e6TableTTwoAt_genActZ)

theorem vecs_getD : ∀ (r V a : Nat), a < r → (vecs V r).getD a [] = vecAt V a
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | r + 1, V, 0, _ => by
    change (digs 3 3 V 6 :: vecs (Nat.shiftRight V 18) r).getD 0 [] = digs 3 3 (V >>> (18 * 0)) 6
    rw [List.getD_cons_zero, Nat.mul_zero, Nat.shiftRight_zero]
  | r + 1, V, a + 1, h => by
    change (digs 3 3 V 6 :: vecs (Nat.shiftRight V 18) r).getD (a + 1) [] =
      digs 3 3 (V >>> (18 * (a + 1))) 6
    rw [List.getD_cons_succ, vecs_getD r _ a (by omega)]
    change digs 3 3 ((V >>> 18) >>> (18 * a)) 6 = _
    rw [← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm]

theorem leafK_zero {k : Nat} {Hs : List (List Nat)} {Os : List (List (List Nat))}
    {V a0 a1 a2 a3 a4 a5 : Nat} (h : leafK k Hs Os V a0 a1 a2 a3 a4 a5 = 0) : rowK k Hs Os (bV V a0 a1 a2 a3 a4 a5) = true := by
  unfold leafK at h
  rw [nIf_eqE] at h
  by_contra hc
  rw [if_neg hc] at h
  exact absurd h one_ne_zero

theorem leafKA2_zero {Hs : List (List Nat)} {Os : List (List (List Nat))}
    {V a0 a1 a2 a3 a4 a5 : Nat} (h : leafKA2 Hs Os V a0 a1 a2 a3 a4 a5 = 0) : rowK 0 Hs Os (bV V a0 a1 a2 a3 a4 a5) = true := by
  unfold leafKA2 at h
  rw [nIf_eqE] at h
  refine rowKA2_sound ?_
  by_contra hc
  rw [if_neg hc] at h
  exact absurd h one_ne_zero

theorem rowK_of_enum (k : Fin 5) {L0 N1 N2 N3 N4 N5 : Nat}
    (hn : nbOK D.GR D.FL k L0 N1 N2 N3 N4 N5 = true)
    {Hs : List (List Nat)} {Os : List (List (List Nat))}
    (leaf : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (hleaf : ∀ a0 a1 a2 a3 a4 a5, leaf a0 a1 a2 a3 a4 a5 = 0 →
      rowK k Hs Os (bV RV.V a0 a1 a2 a3 a4 a5) = true)
    (hm : Nat.beq (enumK D.GR L0 N1 N2 N3 N4 N5 leaf) 0 = true)
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadm : E6Admissible (fun i => ρ (Pi.single i 1)) (repZ k) 2) :
    rowK k Hs Os (bList fun i => ρ (Pi.single i 1)) = true := by
  obtain ⟨a, ha, hle⟩ := e6Admissible_le_enumK k dataOK hn leaf _ hadm
  have h0 : enumK D.GR L0 N1 N2 N3 N4 N5 leaf = 0 := Nat.eq_of_beq_eq_true hm
  have hl := hleaf (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (by omega)
  have hV : vecs RV.V 72 = roots () := beq_iff_eq.1 rootsV
  have e : ∀ i : Fin 6, vecAt RV.V (a i) = List.ofFn (ρ (Pi.single i 1)) := fun i => by
    rw [← vecs_getD 72 _ _ (ha i).1, hV, (ha i).2]
  have hb : bV RV.V (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) = bList fun i => ρ (Pi.single i 1) := by
    unfold bV
    rw [e 0, e 1, e 2, e 3, e 4, e 5]
    rfl
  rw [← hb]
  exact hl

theorem tableAt_of_checks (k : Nat)
    (hk : k < 5) {Hs : List (List Nat)} {Os : List (List (List Nat))}
    {L0 N1 N2 N3 N4 N5 cnt : Nat}
    (hw : wOKK (classes (reps.getD k [])) Hs Os = true) (hs : hsK Hs = true)
    (hr : repOK D.GR D.FL k L0 N1 N2 N3 N4 N5 cnt = true)
    (leaf : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (hleaf : ∀ a0 a1 a2 a3 a4 a5, leaf a0 a1 a2 a3 a4 a5 = 0 →
      rowK k Hs Os (bV RV.V a0 a1 a2 a3 a4 a5) = true)
    (hm : Nat.beq (enumK D.GR L0 N1 N2 N3 N4 N5 leaf) 0 = true) :
    E6TableTTwoAt (repZ ⟨k, hk⟩) :=
  rowK_sound ⟨k, hk⟩ hw hs fun ρ _ _ hadm =>
    rowK_of_enum ⟨k, hk⟩ (bAnd_true hr).1 leaf hleaf hm ρ hadm

public theorem e6TableTTwo_kernel :
    E6TableTTwoStmt := by
  have h0 := tableAt_of_checks 0 (by decide) weylA2 hsA2 enumA2 (leafKA2 W.H0 W.O0 RV.V)
    (fun _ _ _ _ _ _ h => leafKA2_zero h) mapsA2F
  have h1 := tableAt_of_checks 1 (by decide) weylA4A1 hsA4A1 enumA4A1 (leafK 1 W.H1 W.O1 RV.V)
    (fun _ _ _ _ _ _ h => leafK_zero h) mapsA4A1
  have h2 := tableAt_of_checks 2 (by decide) weylD4 hsD4 enumD4 (leafK 2 W.H2 W.O2 RV.V)
    (fun _ _ _ _ _ _ h => leafK_zero h) mapsD4
  have h3 := tableAt_of_checks 3 (by decide) weylA5 hsA5 enumA5 (leafK 3 W.H3 W.O3 RV.V)
    (fun _ _ _ _ _ _ h => leafK_zero h) mapsA5
  have h4 := tableAt_of_checks 4 (by decide) weylD5 hsD5 enumD5 (leafK 4 W.H4 W.O4 RV.V)
    (fun _ _ _ _ _ _ h => leafK_zero h) mapsD5
  have hrep : ∀ k : Fin 5, E6TableTTwoAt (repZ k) := by
    intro k
    fin_cases k
    exacts [h0, h1, h2, h3, h4]
  refine e6TableTTwoStmt_iff.2 fun v => ?_
  by_cases hv : v = 0
  · intro ρ _ _ _ hv0
    exact absurd hv hv0
  · obtain ⟨k, hk⟩ := e6_cover_of_coverK coverOK v hv
    clear hv
    induction hk with
    | refl => exact hrep k
    | tail _ hbc ih =>
      obtain ⟨j, rfl⟩ := hbc
      exact e6TableTTwoAt_genActZ j _ ih

end CertificateChecks.KernelE6TT
