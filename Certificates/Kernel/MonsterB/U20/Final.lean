module

public import CFSG.Certificates.Kernel.MonsterB.U20Sound
public import Certificates.Kernel.MonsterB.U20.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.U20

open CFSG.KC.Co1F2 CFSG.Monster.B.TwoA.Unitary

theorem recList_eq : recList = u20RecRows.toList := by
  simp [recList, u20RecRows]

theorem forall₂_get {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    [Inhabited α] [Inhabited β] (h : List.Forall₂ R l₁ l₂) {i : ℕ} (hi : i < l₁.length) :
    R l₁[i]! l₂[i]! := by
  have hi2 : i < l₂.length := h.length_eq ▸ hi
  have := h.get hi hi2
  simpa [getElem!_pos l₁ i hi, getElem!_pos l₂ i hi2] using this

theorem flat_len : CFSG.KD.U20.F.c0.length = 400 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem getElem!_toList {α : Type} [Inhabited α] (a : Array α) (j : ℕ) : a[j]! = a.toList[j]! := by
  cases a
  simp

theorem rec_size : u20RecRows.size = 400 := by
  rw [← Array.length_toList, ← recList_eq, ← (flatK_sound flat_ok).length_eq, flat_len]

theorem rec_get {j : ℕ} (hj : j < 400) :
    CFSG.KD.U20.F.c0[j]! < 2 ^ 400 ∧ u20RecRows[j]! = unpackR 20 CFSG.KD.U20.F.c0[j]! := by
  have h := forall₂_get (flatK_sound flat_ok) (i := j) (by rw [flat_len]; exact hj)
  rw [recList_eq] at h
  exact ⟨h.1, (getElem!_toList u20RecRows j).trans h.2⟩

theorem records_ok : ∀ j < 400, wordRows u20Words[j]! = u20RecRows[j]! := by
  intro j hj
  have hW := wordsK_sound words_ok
  have hwl : j < u20Words.toList.length := by
    rw [hW.length_eq, flat_len]
    exact hj
  have h := forall₂_get hW hwl
  rw [getElem!_toList u20Words j, wordRows_eq (gensK_sound gens_ok) _ h.1, h.2, (rec_get hj).2]

theorem map_get! {a : Array (Array ℕ)} {f : Array ℕ → ℕ} {j : ℕ} (h : j < a.size) :
    (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos _ j (by rw [Array.size_map]; exact h), Array.getElem_map, getElem!_pos a j h]

theorem flat_get {j : ℕ} (hj : j < 400) :
    (u20RecRows.map flatRows)[j]! = CFSG.KD.U20.F.c0[j]! := by
  rw [map_get! (rec_size ▸ hj : j < u20RecRows.size), (rec_get hj).2,
    flatRows_unpackR (rec_get hj).1]

theorem cert_ok : ∀ c < 400, combRows unitCert[c]! = eRows c := by
  intro c hc
  have hR : ∀ j < 400, u20RecRows[j]! = unpackR 20 (u20RecRows.map flatRows)[j]! := fun j hj => by
    rw [flat_get hj]
    exact (rec_get hj).2
  have hsel := selK_eq flat_len (fun j hj => flat_get hj)
  have hinv := invK_sound inv_ok
  have hD : ∀ c < 400, selXor 400 (u20RecRows.map flatRows) (CFSG.KD.U20.D.c0[c]!) = 2 ^ c :=
    fun c hc => by rw [← hsel, hinv.2 c hc]
  rw [combRows_eq hR, unitCert, gaussInv_spec 400 _ _ hD c hc, eRows_eq hc]

end CFSG.KC.U20

end
