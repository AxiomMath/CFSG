
module

public import Certificates.Kernel.Sporadic.Fi24G2g.Triple
public import Certificates.Kernel.Sporadic.Fi24G2g.Reps
public import Certificates.Kernel.Sporadic.Fi24G2d.Final

public section

namespace CertificateChecks.KernelFi24G2g

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix CertificateChecks.KernelFi24Orb
  CertificateChecks.KernelFi24G2e TauCeti TauCeti.Sporadic CFSG.KC.Fi24FixK CFSG.KC.Fi24FixS

open CFSG.Sporadic.Fi24 (R cls D24)
open CFSG.KD.Fi24Orb (NM NI)
open CFSG.KD.Fi24G2e (CWL)
open CFSG.Sporadic.FischerOddCore (rep7)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction

section D

theorem card_fixed_pts (r : R) :
    Nat.card {x : D24 // r * x * r⁻¹ = x} = Nat.card {k : Fin 306936 // r • k = k} := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv CFSG.Sporadic.Fi24.clsEquiv fun k => ?_)
  rw [CFSG.Sporadic.Fi24.clsEquiv_apply, ← CFSG.Sporadic.Fi24.cls_smul_R]
  exact ⟨fun h => by rw [h], fun h => CFSG.Sporadic.Fi24.cls_injective h⟩

theorem card_fixed_conj {r r' c : R} (hc : c * r * c⁻¹ = r') :
    Nat.card {x : D24 // r * x * r⁻¹ = x} = Nat.card {x : D24 // r' * x * r'⁻¹ = x} := by
  rw [card_fixed_pts, card_fixed_pts]
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun k => ?_)
  rw [MulAction.toPerm_apply, ← hc, mul_smul, mul_smul, inv_smul_smul]
  exact ⟨fun h => by rw [h], fun h => smul_left_cancel c h⟩

end D

theorem card_fin_filter (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    Nat.card {r : Fin n // p r.val} = ((Finset.range n).filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun r _ => r.val) (fun r hr => ?_) (fun a _ b _ h => Fin.ext h)
    (fun b hb => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp [hr]
  · simp only [Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

theorem cwl_lt {i : ℕ} (hi : i < 7) : ∀ g ∈ CWL i, g < 12 := by
  interval_cases i <;> decide +kernel

section Bind

variable (hP : PtRank)
include hP

theorem fixed_iff_walk {w : List ℕ} (hw : ∀ g ∈ w, g < 12) (k : Fin 306936) :
    ρ (wp w) • k = k ↔ walk CFSG.KD.Fi24Fix.TG w (NM k) = NM k := by
  have e : (ρ (wp w))⁻¹ • k = pk (walk_lt hw (NM_lt k.isLt)) := by
    conv_lhs => rw [← pk_NM k]
    exact smul_pk hP hw _
  have hi : ρ (wp w) • k = k ↔ (ρ (wp w))⁻¹ • k = k := by
    rw [inv_smul_eq_iff, eq_comm]
  rw [hi, e]
  constructor
  · intro h
    exact pk_inj _ _ (h.trans (pk_NM k).symm)
  · intro h
    rw [pk_congr _ (NM_lt k.isLt) h, pk_NM]

theorem card_fixed_word {w : List ℕ} (hw : ∀ g ∈ w, g < 12) :
    Nat.card {x : D24 // ρ (wp w) * x * (ρ (wp w))⁻¹ = x} =
      ((Finset.range 306936).filter fun r => walk CFSG.KD.Fi24Fix.TG w r = r).card := by
  rw [card_fixed_pts, ← card_fin_filter]
  have hb : Function.Bijective fun k : Fin 306936 => (⟨NM k, NM_lt k.isLt⟩ : Fin 306936) :=
    (Finite.injective_iff_bijective).1 fun a b h =>
      Fin.ext (NM_inj a.isLt b.isLt (congrArg Fin.val h))
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hb) fun k => ?_)
  rw [fixed_iff_walk hP hw]
  rfl

theorem card_fixed_rep7 {i : ℕ} (hi : i < 7) :
    Nat.card {x : D24 // rep7 i * x * (rep7 i)⁻¹ = x} =
      [3512, 3512, 504, 31672, 31672, 696, 696].getD i 0 := by
  obtain ⟨c, hc⟩ := conj_rep7 hi
  rw [card_fixed_conj hc, card_fixed_word hP (cwl_lt hi)]
  have hA : CWL 0 = CFSG.KD.Fi24G2d.W2A ∧ CWL 1 = CFSG.KD.Fi24G2d.W2A ∧
      CWL 2 = CFSG.KD.Fi24G2d.W2B ∧ CWL 3 = CFSG.KD.Fi24G2d.W2C ∧ CWL 4 = CFSG.KD.Fi24G2d.W2C ∧
      CWL 5 = CFSG.KD.Fi24G2d.W2D ∧ CWL 6 = CFSG.KD.Fi24G2d.W2D := by decide +kernel
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hA
  interval_cases i
  · rw [h0]; exact CFSG.KD.Fi24G2d.card_fix_W2A
  · rw [h1]; exact CFSG.KD.Fi24G2d.card_fix_W2A
  · rw [h2]; exact CFSG.KD.Fi24G2d.card_fix_W2B
  · rw [h3]; exact CFSG.KD.Fi24G2d.card_fix_W2C
  · rw [h4]; exact CFSG.KD.Fi24G2d.card_fix_W2C
  · rw [h5]; exact CFSG.KD.Fi24G2d.card_fix_W2D
  · rw [h6]; exact CFSG.KD.Fi24G2d.card_fix_W2D

end Bind

end CertificateChecks.KernelFi24G2g

end
