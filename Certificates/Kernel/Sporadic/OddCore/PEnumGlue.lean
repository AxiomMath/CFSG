module

public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

namespace CFSG.KS.PEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin

theorem strictB_app' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem penumSl_spec {n w m nw k cnt lo len : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumSlK n w m nw conj G GI k cnt T PL POS SRT SRI lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt →
      penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i = true := by
  intro i h1 h2 h3
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_app'] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  exact h'

theorem penumPt_canon {n w m nw k cnt i : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i = true) :
    canonK n w m nw (T i) = true := by
  unfold penumPtK at h
  rw [strictB_app'] at h
  exact ((bAnd_iff _ _).1 h).1

@[expose] noncomputable def gensK (gs : Array (Array Nat)) (n w k : Nat) (G : Nat → Nat) : Bool :=
  bAnd(Nat.beq gs.size k, allN k (fun j => bAnd(bindArrK gs[j]! n w (G j),
    canonK n w (mask w) (n * w) (G j))))

theorem gensOK_of {gs : Array (Array Nat)} {n w k : Nat} {G : Nat → Nat}
    (h : gensK gs n w k G = true) : GensOK n w k G gs := by
  unfold gensK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun j hj => ?_⟩
  obtain ⟨hb, hc⟩ := (bAnd_iff _ _).1 (allN_spec h2 j hj)
  exact ⟨unpack_eq_of_bindArrK hb, hc⟩

theorem unpack_size (n w p : Nat) : (unpack n w p).size = n := by
  simp [unpack]

theorem beq_unpack {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    (unpack n w p == unpack n w q) = Nat.beq p q := by
  rw [← eqA_unpack hp hq]
  cases h : CFSG.Monster.B.Co2.Native.eqA n (unpack n w p) (unpack n w q)
  · have hne : unpack n w p ≠ unpack n w q := fun e => by
      rw [e] at h
      have := (CertificateChecks.KernelSpor.OddCore.eqA_iff n (unpack n w q) (unpack n w q)).2
        (fun _ _ => rfl)
      rw [this] at h
      exact absurd h (by decide)
    simpa using hne
  · have he : unpack n w p = unpack n w q := by
      apply Array.ext (by rw [unpack_size, unpack_size])
      intro i hi _
      have := (CertificateChecks.KernelSpor.OddCore.eqA_iff n _ _).1 h i (by rwa [unpack_size] at hi)
      have hi' : i < (unpack n w q).size := by
        rw [unpack_size] at hi ⊢
        exact hi
      rwa [getElem!_pos _ i hi, getElem!_pos _ i hi'] at this
    simp [he]

theorem filter_ofFn {α : Type} (m : Nat) (f : Nat → α) (p : α → Bool) :
    (Array.ofFn (n := m) fun i => f i.val).filter p =
      (((List.range m).filter fun i => p (f i)).map f).toArray := by
  have e : List.ofFn (fun i : Fin m => f i.val) = (List.range m).map f := by
    apply List.ext_getElem <;> simp
  apply Array.toList_inj.1
  simp only [Array.toList_filter, Array.toList_ofFn, e, List.filter_map]
  simp [Function.comp_def]

end CFSG.KS.PEnum

end
