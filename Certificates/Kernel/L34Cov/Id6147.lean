module

public import Certificates.Kernel.L34Cov.Id6147Checks
public import Certificates.Kernel.L34Cov.Lift22212

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.OddStandard.ONanRec.IdCert
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W CFSG.KC.L34KSnd
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelL34W

theorem tgT_eq (m : ℕ) : tgT m = unpack 42 6 (tK m) ∧ Cn (tK m) :=
  ⟨(tgK_eq gensG m).2, (tgK_eq gensG m).1⟩

theorem cnMul {a b : ℕ} (ha : Cn a) (hb : Cn b) : Cn (mulK a b) :=
  CFSG.KC.BfsPin.canonK_pcomp ha hb

theorem comp_eqK {a b : ℕ} (ha : Cn a) (hb : Cn b) :
    comp 42 (unpack 42 6 a) (unpack 42 6 b) = unpack 42 6 (mulK a b) :=
  comp_unpack' ha hb

theorem comT_eq {a b : ℕ} (ha : Cn a) (hb : Cn b) :
    comT (unpack 42 6 a) (unpack 42 6 b) = comK a b := by
  unfold comT
  rw [comp_eqK ha hb, comp_eqK hb ha, beq_unpack (cnMul ha hb) (cnMul hb ha)]
  rfl

theorem r4_eqK : r₄T () = unpack 42 6 (vK 2) ∧ Cn (vK 2) := by
  have e : r₄T () = comp 42 r₂T r₃T := rfl
  rw [e, gT4.1, gT5.1, comp_eqK gT4.2 gT5.2]
  exact ⟨rfl, cnMul gT4.2 gT5.2⟩

theorem not_true' {x : Bool} (h : (!x) = true) : x = false := by
  cases x
  · rfl
  · exact absurd h (by decide)

theorem q8_of {p m₁ m₂ : ℕ} (hp : Cn p) (h : q8PairT (unpack 42 6 p) m₁ m₂ = true) :
    q8K p m₁ m₂ = true := by
  obtain ⟨e1, c1⟩ := tgT_eq m₁
  obtain ⟨e2, c2⟩ := tgT_eq m₂
  unfold q8PairT at h
  rw [e1, e2, comT_eq c1 hp, comT_eq c2 hp, comp_eqK c1 c1, comp_eqK c2 c2, idTab42,
    beq_unpack (cnMul c1 c1) cn_pidn, beq_unpack (cnMul c1 c1) (cnMul c2 c2), comT_eq c1 c2] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  unfold q8K
  exact andB_iff.2 ⟨h1, andB_iff.2 ⟨h2, andB_iff.2 ⟨notB_iff.2 (not_true' h3),
    andB_iff.2 ⟨h4, notB_iff.2 (not_true' h5)⟩⟩⟩⟩

theorem sigmaCase_of {p : ℕ} (hp : Cn p) (h : sigK p = true) :
    sigmaCase (unpack 42 6 p) = true := by
  unfold sigK at h
  unfold sigmaCase
  rw [Bool.or_eq_true, Bool.or_eq_true]
  rcases orB_iff.1 h with h1 | h2
  · left
    left
    rw [notB_iff] at h1
    rw [comp_eqK hp hp, idTab42, beq_unpack (cnMul hp hp) cn_pidn]
    change (!Nat.beq (mulK p p) (pidn 42 6)) = true
    rw [h1]
    rfl
  · rcases orB_iff.1 h2 with h3 | h4
    · right
      obtain ⟨m, hm, hb⟩ := List.any_eq_true.1 h3
      refine List.any_eq_true.2 ⟨m, hm, ?_⟩
      obtain ⟨e, c⟩ := tgT_eq m
      rw [e, r4_eqK.1, comp_eqK c hp, comp_eqK r4_eqK.2 c,
        beq_unpack (cnMul c hp) (cnMul r4_eqK.2 c)]
      exact hb
    · left
      right
      rw [notB_iff] at h4
      cases hq : (List.range 64).any fun m₁ => (List.range 64).any fun m₂ =>
          q8PairT (unpack 42 6 p) m₁ m₂
      · rfl
      · exfalso
        obtain ⟨m₁, r₁, hq1⟩ := List.any_eq_true.1 hq
        obtain ⟨m₂, r₂, hq2⟩ := List.any_eq_true.1 hq1
        have hk := q8_of hp hq2
        have hk' := hk
        unfold q8K at hk'
        obtain ⟨c1, hk'⟩ := andB_iff.1 hk'
        obtain ⟨c2, -⟩ := andB_iff.1 hk'
        have hm₁ : m₁ ∈ cK p := List.mem_filter.2 ⟨r₁, c1⟩
        have hm₂ : m₂ ∈ cK p := List.mem_filter.2 ⟨r₂, c2⟩
        have : ((cK p).any fun m₁ => (cK p).any fun m₂ => q8K p m₁ m₂) = true :=
          List.any_eq_true.2 ⟨m₁, hm₁, List.any_eq_true.2 ⟨m₂, hm₂, hk⟩⟩
        rw [h4] at this
        exact absurd this (by decide)

theorem sigmaOK_k : sigmaOK = true := by
  unfold sigmaOK
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have hj := allN' (allN' ch6147s_k k hk)
  obtain ⟨e, c⟩ := tgT_eq k
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [e, gT4.1, comp_eqK c gT4.2]
    exact sigmaCase_of (cnMul c gT4.2) (hj 0 (by norm_num))
  · rw [e, gT5.1, comp_eqK c gT5.2]
    exact sigmaCase_of (cnMul c gT5.2) (hj 1 (by norm_num))
  · rw [e, r4_eqK.1, comp_eqK c r4_eqK.2]
    exact sigmaCase_of (cnMul c r4_eqK.2) (hj 2 (by norm_num))

theorem centOK_k : centOK = true := by
  have key : ∀ m j, comT (tgT m) (tgT j) = comK (tK m) (tK j) := fun m j => by
    rw [(tgT_eq m).1, (tgT_eq j).1, comT_eq (tgT_eq m).2 (tgT_eq j).2]
  unfold centOK
  simp only [key]
  exact ch6147c_k

theorem facts6147 :
    sigmaOK = true ∧ centOK = true ∧
    ∀ s ∈ idSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2)) := by
  refine ⟨sigmaOK_k, centOK_k, fun s hs => ?_⟩
  change cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  rw [cv_zword]
  simp only [idSpecs, idCommData, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact cv_eq_of_cvId ch6147l_k.1
  · exact cv_eq_of_cvId ch6147l_k.2.1
  · exact cv_eq_of_cvId ch6147l_k.2.2

end CertificateChecks.KernelL34Cov

end
