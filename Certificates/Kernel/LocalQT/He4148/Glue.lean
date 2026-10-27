module

public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.PrimSound

public section

namespace CertificateChecks.KernelLQT.He4148

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.HeldB CFSG.KC.BfsPin

@[expose] noncomputable def bindsK (n w : Nat) (PS PSI : Nat → Nat) (l : List (Array Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih j => bAnd(bindListK n w (PS j) t.toList,
      bAnd(invEqK n w (mask w) (n * w) (PS j) (PSI j),
      bAnd(invEqK n w (mask w) (n * w) (PSI j) (PS j),
      bAnd(canonK n w (mask w) (n * w) (PS j),
      bAnd(canonK n w (mask w) (n * w) (PSI j), ih (Nat.succ j))))))) l

@[expose] def BindAt (n w : Nat) (P PI : Nat) (t : Array Nat) : Prop :=
  bindListK n w P t.toList = true ∧ invEqK n w (mask w) (n * w) P PI = true ∧
    invEqK n w (mask w) (n * w) PI P = true ∧ canonK n w (mask w) (n * w) P = true ∧
    canonK n w (mask w) (n * w) PI = true

theorem bindsK_spec {n w : Nat} {PS PSI : Nat → Nat} :
    ∀ {l : List (Array Nat)} {i : Nat}, bindsK n w PS PSI l i = true →
      ∀ j < l.length, BindAt n w (PS (i + j)) (PSI (i + j)) (l.getD j #[])
  | [], _, _, j, h => absurd h (Nat.not_lt_zero j)
  | t :: l, i, hb, j, hj => by
    have hb' : bAnd(bindListK n w (PS i) t.toList,
      bAnd(invEqK n w (mask w) (n * w) (PS i) (PSI i),
      bAnd(invEqK n w (mask w) (n * w) (PSI i) (PS i),
      bAnd(canonK n w (mask w) (n * w) (PS i),
      bAnd(canonK n w (mask w) (n * w) (PSI i), bindsK n w PS PSI l (Nat.succ i)))))) = true := hb
    simp only [bAnd_iff] at hb'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb'
    rcases j with _ | j
    · exact ⟨h1, h2, h3, h4, h5⟩
    · have := bindsK_spec h6 j (by simpa using hj)
      rw [Nat.succ_add, ← Nat.add_succ] at this
      simpa using this

theorem unpack_size' (n w P : Nat) : (unpack n w P).size = n := by
  simp [unpack]

theorem imageList_of_rep {n : Nat} {t : Array Nat} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (h : Rep n t g) : CFSG.Monster.B.Mathieu.imageList g = t.toList := by
  apply List.ext_getElem
  · simp [CFSG.Monster.B.Mathieu.imageList, ht]
  · intro i h1 h2
    have hi : i < n := by simpa [CFSG.Monster.B.Mathieu.imageList] using h1
    simp only [CFSG.Monster.B.Mathieu.imageList, List.getElem_ofFn, Array.getElem_toList]
    rw [← h.apply hi, getElem!_pos t i (by omega)]

theorem unpack_facts {n w P PI : Nat} {t : Array Nat} (ht : t = unpack n w P)
    (h1 : invEqK n w (mask w) (n * w) P PI = true) (h2 : invEqK n w (mask w) (n * w) PI P = true) :
    permChk n t = true ∧ Rep n (unpack n w P) (permOrId n t) ∧
      Rep n (unpack n w PI) (permOrId n t)⁻¹ := by
  subst ht
  obtain ⟨e1, e2⟩ := invEqK_sound h1
  obtain ⟨-, e4⟩ := invEqK_sound h2
  have hc : permChk n (unpack n w P) = true := by
    unfold permChk
    rw [e1, e2, e4]
    rfl
  obtain ⟨r1, r2⟩ := permChk_spec hc
  rw [e1] at r2
  exact ⟨hc, r1, r2⟩

theorem bind_facts {n w P PI : Nat} {t : Array Nat} (h : BindAt n w P PI t) :
    t = unpack n w P ∧ permChk n t = true ∧ Rep n (unpack n w P) (permOrId n t) ∧
      Rep n (unpack n w PI) (permOrId n t)⁻¹ := by
  have ht : t = unpack n w P := by
    rw [← toArray_eq_of_bindListK h.1, Array.toArray_toList]
  exact ⟨ht, unpack_facts ht h.2.1 h.2.2.1⟩

theorem imageList_bind {n w P PI : Nat} {t : Array Nat} (h : BindAt n w P PI t) :
    CFSG.Monster.B.Mathieu.imageList (permOrId n t) = (unpack n w P).toList :=
  imageList_of_rep (unpack_size' n w P) (bind_facts h).2.2.1

theorem rep_pcomp {n w P Q : Nat} {g h : Equiv.Perm (Fin n)}
    (hP : canonK n w (mask w) (n * w) P = true) (hQ : canonK n w (mask w) (n * w) Q = true)
    (hg : Rep n (unpack n w P) g) (hh : Rep n (unpack n w Q) h) :
    Rep n (unpack n w (pcomp n w (mask w) P Q)) (g * h) := by
  rw [← compA_unpack hP hQ]
  exact rep_compA hg hh

theorem getD_map_lt {α β : Type*} (f : α → β) {l : List α} (d : α) (d' : β) {j : Nat}
    (hj : j < l.length) : (l.map f).getD j d' = f (l.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getD_eq_getElem _ _ hj]

end CertificateChecks.KernelLQT.He4148

end
