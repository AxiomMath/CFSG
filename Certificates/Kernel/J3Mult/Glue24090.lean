module

public import Certificates.Kernel.J3Mult.Words24090
public import CFSG.Sporadic.J3
public import CFSG.Certificates.Kernel.TabMatGrpSound

public section

namespace CertificateChecks.KernelJ3Mult.Glue24090

open CFSG.KC.TabMatGrp CertificateChecks.KernelLC.J3Ops CFSG.Sporadic.Recognition.J3Multiplier
open CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Certificates
open CFSG.Sporadic.J3 (a b J rep_a rep_b j3Facts)
open CFSG.Sporadic.J3.Native (j3Data)
open CFSG.Sporadic.Th (Rep)
open CFSG.Sporadic.Th.Native

section Tables

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {x y : G} {α αi β βi : Table}

theorem size_wordTab (v : List (ℕ × Bool)) : (wordTab n α αi β βi v).size = n := by
  cases v with
  | nil => simp [wordTab, idT]
  | cons l v => simp [wordTab, compT]

theorem eq_idT_of_rep (hn : n < 2 ^ 32) {T : Table} (hs : T.size = n) (hT : Rep n T (1 : G)) :
    T = idT n := by
  have hI := Rep.idT (G := G) hn
  apply Array.ext
  · rw [hs]
    simp [idT]
  · intro i h1 h2
    have hi : i < n := hs ▸ h1
    have e := (hT i hi).trans (hI i hi).symm
    unfold ap at e
    rw [getElem!_pos T i h1, getElem!_pos (idT n) i h2] at e
    exact UInt32.toNat_inj.mp e

theorem relCheck_of_words (hn : n < 2 ^ 32) (hx : Rep n α x) (hxi : Rep n αi x⁻¹)
    (hy : Rep n β y) (hyi : Rep n βi y⁻¹) {rels : List (List (ℕ × Bool))}
    (h : ∀ v ∈ rels, CFSG.Sporadic.Bridge.wordProd (img2 x y) v = 1) :
    relCheck n α αi β βi rels = true := by
  unfold relCheck
  rw [List.all_eq_true]
  intro v hv
  have hr := rep_wordTab hn hx hxi hy hyi v
  rw [h v hv] at hr
  rw [eq_idT_of_rep hn (size_wordTab v) hr]
  exact beq_self_eq_true _

end Tables

theorem MatP_A : MatP 80 SA.M = CFSG.Sporadic.J3.mA j3Data := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound SA.bind, ← SA.eq]
  exact CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload _ _

theorem MatP_B : MatP 80 SB.M = CFSG.Sporadic.J3.mB j3Data := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound SB.bind, ← SB.eq]
  exact CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload _ _

theorem dets : (CFSG.Sporadic.J3.mA j3Data).det ≠ 0 ∧ (CFSG.Sporadic.J3.mB j3Data).det ≠ 0 := by
  rw [← MatP_A, ← MatP_B]
  exact seedsK_det Words24090.ch24090_words

noncomputable abbrev σ : Fin 2 → J j3Data := ![a j3Data, b j3Data]

theorem hA : MatP 80 SA.M = matOf (J j3Data).subtype (σ 0) := by
  have e : (σ 0 : J j3Data) = a j3Data := rfl
  rw [e, matOf, Subgroup.subtype_apply, CFSG.Sporadic.J3.coe_a, CFSG.Sporadic.J3.gA,
    dif_pos dets.1, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_A]

theorem hB : MatP 80 SB.M = matOf (J j3Data).subtype (σ 1) := by
  have e : (σ 1 : J j3Data) = b j3Data := rfl
  rw [e, matOf, Subgroup.subtype_apply, CFSG.Sporadic.J3.coe_b, CFSG.Sporadic.J3.gB,
    dif_pos dets.2, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_B]

theorem gen_words {w : List (Fin 2 × Bool)} (hw : w ∈ checkWords) :
    signedProd (fun i : Fin 2 => segVal σ genWords i.val) w = 1 := by
  have hm : (w, ([] : List (Fin 2 × Bool))) ∈ Words24090.relPs checkWords :=
    List.mem_map.2 ⟨w, hw, rfl⟩
  have h := grpK_sound Subtype.val_injective hA hB genWords (by decide)
    (Words24090.relPs checkWords) Words24090.ch24090_words _ hm
  rwa [signedProd_nil, mul_one] at h

theorem img2_eq : (fun i : Fin 2 => img2 (a j3Data) (b j3Data) i.val) = σ := by
  funext i
  fin_cases i <;> rfl

theorem segVal_gen : (fun i : Fin 2 => segVal σ genWords i.val) =
    fun i : Fin 2 => FreeGroup.lift σ (FreeGroup.mk (genWords.getD i.val [])) := by
  funext i
  exact (lift_mk_eq_signedProd σ _).symm

theorem natWords_one :
    ∀ v ∈ natWords, CFSG.Sporadic.Bridge.wordProd (img2 (a j3Data) (b j3Data)) v = 1 := by
  intro v hv
  rw [natWords, List.map_map, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  have h := gen_words hw
  rw [segVal_gen, ← lift_mk_eq_signedProd] at h
  rw [Function.comp_apply, ← CFSG.LieType.Multipliers.lift_mk_eq_wordProd, img2_eq,
    ← CFSG.Sporadic.Recognition.CoverTransfer.lift_mk_substWord]
  exact h

theorem j3RelCheck_eq (D : CFSG.Sporadic.J3.Native.Data) (rels : List (List (ℕ × Bool))) :
    j3RelCheck D rels = relCheck D.n D.tA (invT D.n D.tA) D.tB (invT D.n D.tB) rels :=
  rfl

theorem rel_check : j3RelCheck j3Data natWords = true := by
  have hA := rep_a j3Facts.orbitFacts
  have hB := rep_b j3Facts.orbitFacts
  rw [j3RelCheck_eq]
  exact relCheck_of_words (lt_trans j3Facts.n_lt (by norm_num)) hA
    (Rep.inv_of_invOK hA j3Facts.invA) hB (Rep.inv_of_invOK hB j3Facts.invB) natWords_one

end CertificateChecks.KernelJ3Mult.Glue24090

end
