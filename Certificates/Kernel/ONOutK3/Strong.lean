module

public import Certificates.Kernel.Sporadic.ON3.Words
public import CFSG.Certificates.Kernel.Spor.PointChainCard
public import Certificates.Data.GrSLitL34FactsCF23ONOutK3Data

public section

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.ComponentClassification.SolMax.ONOut
open CFSG.Sporadic.ON.Native (nPts)

variable {n : Nat}

theorem prep_pinv {t : Array Nat} {g : Equiv.Perm (Fin n)} (hs : t.size = n) (ht : PRep n t g) :
    PRep n (pinvCand n t) g⁻¹ := by
  have he : t = Array.ofFn (n := n) fun i => t[i.val]! :=
    CFSG.KS.PW.arr_ext hs fun x _ => rfl
  intro x
  rw [he]
  have hT : ∀ y < n, t[y]! < n := fun y hy => ht.lt hy
  have hUT : ∀ y < n, (fun z => if h : z < n then (g⁻¹ ⟨z, h⟩ : Nat) else 0) (t[y]!) = y := by
    intro y hy
    simp only
    rw [dif_pos (hT y hy)]
    have : (⟨t[y]!, hT y hy⟩ : Fin n) = g ⟨y, hy⟩ := Fin.ext (ht.apply hy)
    rw [this]
    simp
  rw [CFSG.KS.CB.pinvCand_get (T := fun i => t[i]!)
    (U := fun z => if h : z < n then (g⁻¹ ⟨z, h⟩ : Nat) else 0) hT hUT x.2, dif_pos x.2]

theorem pisInv_of_prep {t r : Array Nat} {g : Equiv.Perm (Fin n)} (ht : PRep n t g)
    (hr : PRep n r g⁻¹) : pisInv n t r = true := by
  unfold pisInv
  rw [allBelowN_iff]
  intro i hi
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr.apply (g ⟨i, hi⟩).2]
  simp

theorem prep_perm_of {t : Array Nat} {g : Equiv.Perm (Fin n)} (hs : t.size = n) (ht : PRep n t g) :
    PRep n t (permOfArr n t) :=
  (prep_permOfArr (pisInv_of_prep ht (prep_pinv hs ht))).1

theorem W_size : Data.strongWords.size = 7 := rfl

theorem W_letters : ∀ j < Data.strongWords.size, 2 ≤ j → plettersOK j Data.strongWords[j]! = true := by
  decide

theorem wA_letters : plettersOK 7 wA = true := by decide
theorem wB_letters : plettersOK 7 wB = true := by decide

theorem qon_prep {h : Nat} (hh : h < 7) :
    PRep nPts qonStrongArrs[h]! (permOfArr nPts qonStrongArrs[h]!) ∧
      PRep nPts qonInvArrs[h]! (permOfArr nPts qonStrongArrs[h]!)⁻¹ := by
  apply prep_permOfArr
  unfold pisInv
  rw [allBelowN_iff]
  intro i hi
  obtain ⟨e1, e2, e3, -⟩ := CertificateChecks.KernelSpor.ON3.qon_letters h hh i hi
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, e1]
  refine ⟨e3, ?_⟩
  rw [(CertificateChecks.KernelSpor.ON3.qon_letters h hh _ e3).2.1]
  exact (CertificateChecks.KernelSpor.ON.perm_facts' i hi h hh).2.2

theorem wordArr_prep {w : List Int} (hw : plettersOK 7 w = true) :
    PRep nPts (wordArr w) (permOfArr nPts (wordArr w)) := by
  have := prep_pword (n := nPts) (gs := fun h => permOfArr nPts qonStrongArrs[h]!) (j := 7)
    (fun h hh => (qon_prep hh).1) (fun h hh => (qon_prep hh).2) w hw
  exact prep_perm_of (CFSG.KS.PW.pword_size w) this

theorem sig_facts :
    (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords).size = Data.strongWords.size ∧
      (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[0]! = wordArr wA ∧
      (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[1]! = wordArr wB ∧
      ∀ j < Data.strongWords.size, 2 ≤ j → (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[j]! =
        pword nPts (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)
          (pinvs nPts (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)) Data.strongWords[j]! :=
  CFSG.KS.PCC.strongArrs_facts (by decide) W_letters

theorem sig_size : sigStrong.size = 7 := sig_facts.1

theorem sig_size' {j : Nat} (hj : j < 7) : (sigStrong[j]!).size = nPts := by
  rcases Nat.lt_or_ge j 2 with h | h
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · change (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[0]!.size = nPts
      rw [sig_facts.2.1]
      exact CFSG.KS.PW.pword_size _
    · change (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[1]!.size = nPts
      rw [sig_facts.2.2.1]
      exact CFSG.KS.PW.pword_size _
  · change (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[j]!.size = nPts
    rw [sig_facts.2.2.2 j (by rw [W_size]; exact hj) h]
    exact CFSG.KS.PW.pword_size _

theorem sigInv_get {j : Nat} (hj : j < 7) : (pinvs nPts sigStrong)[j]! = pinvCand nPts sigStrong[j]! := by
  unfold pinvs
  rw [getElem!_pos _ j (by simpa [sig_size] using hj), Array.getElem_map,
    ← getElem!_pos sigStrong j (by simpa [sig_size] using hj)]

theorem sig_prep : ∀ j < 7, PRep nPts sigStrong[j]! (permOfArr nPts sigStrong[j]!) := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj
    suffices ∃ g, PRep nPts sigStrong[j]! g by
      obtain ⟨g, hg⟩ := this
      exact prep_perm_of (sig_size' hj) hg
    rcases Nat.lt_or_ge j 2 with h | h
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · have := wordArr_prep wA_letters
        rw [← sig_facts.2.1] at this
        exact ⟨_, this⟩
      · have := wordArr_prep wB_letters
        rw [← sig_facts.2.2.1] at this
        exact ⟨_, this⟩
    · have hw : sigStrong[j]! = pword nPts sigStrong (pinvs nPts sigStrong) Data.strongWords[j]! :=
        sig_facts.2.2.2 j (by rw [W_size]; exact hj) h
      have := prep_pword (gs := fun h => permOfArr nPts sigStrong[h]!) (j := j)
        (fun h hh => ih h hh (by omega))
        (fun h hh => by
          change PRep nPts (pinvs nPts sigStrong)[h]! _
          rw [sigInv_get (by omega)]
          exact prep_pinv (sig_size' (by omega)) (ih h hh (by omega)))
        _ (W_letters j (by rw [W_size]; exact hj) h)
      rw [← hw] at this
      exact ⟨_, this⟩

theorem peq_self {t : Array Nat} {g : Equiv.Perm (Fin n)} (ht : PRep n t g) : peq n t t = true :=
  (peq_iff ht ht).2 rfl

theorem sig_strong : strongOK nPts (wordArr wA) (wordArr wB) sigStrong Data.strongWords = true := by
  unfold strongOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allBelowN_iff, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨by decide, sig_facts.1⟩, ?_⟩, ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩
  · rw [show sigStrong[0]! = wordArr wA from sig_facts.2.1]
    exact peq_self (wordArr_prep wA_letters)
  · rw [show sigStrong[1]! = wordArr wB from sig_facts.2.2.1]
    exact peq_self (wordArr_prep wB_letters)
  · rw [sig_size] at hj
    rw [sigInv_get hj]
    exact pisInv_of_prep (sig_prep j hj) (prep_pinv (sig_size' hj) (sig_prep j hj))
  · rw [sig_size] at hj
    rcases Nat.lt_or_ge j 2 with h | h
    · exact Or.inl h
    · right
      refine ⟨W_letters j (by rw [W_size]; exact hj) h, ?_⟩
      have hw := sig_facts.2.2.2 j (by rw [W_size]; exact hj) h
      have := peq_self (sig_prep j hj)
      change peq nPts (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[j]!
        (pword nPts (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)
          (pinvs nPts (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)) Data.strongWords[j]!) = true
      change peq nPts (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[j]!
        (strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords)[j]! = true at this
      rw [← hw]
      exact this

end CertificateChecks.KernelSpor.ONK3

end
