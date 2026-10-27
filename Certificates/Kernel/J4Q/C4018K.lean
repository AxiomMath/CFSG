module

public import Certificates.Kernel.J4Q.Mask
public import Certificates.Kernel.J4Q.MaskActData
public import CFSG.Sporadic.J4.QTOutActNative
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Data.List.Nodup
public import Certificates.Kernel.J4Q.Orbits

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT

theorem rowsXor_congr {r r' : Nat → Nat} (c : Nat) :
    ∀ {m : Nat}, (∀ j < m, r j = r' j) → rowsXor r m c = rowsXor r' m c
  | 0, _ => rfl
  | m + 1, h => by
    have ih := rowsXor_congr (r := r) (r' := r') c (m := m) fun j hj => h j (by omega)
    unfold rowsXor at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih, List.foldl_cons, List.foldl_cons,
      List.foldl_nil, List.foldl_nil, h m (by omega)]

theorem tpL_chk : decide ((List.range 23).map tp = mkTPL) = true := by quickRfl

theorem tpL_eq : tpL = mkTPL := of_decide_eq_true tpL_chk

theorem tp_eq {n : Nat} (hn : n < 23) : tp n = mkTPL.getD n [] := by
  rw [← tpL_eq, tpL, List.getD_eq_getElem _ _ (by simpa using hn)]
  simp

theorem kvec_chk : decide (∀ i ∈ List.range 11, actT (mkTPL.getD i []) 1 = mkKV.getD i 0) = true := by
  quickRfl

theorem kcomb_eq (μ : Nat) : kcomb μ = actN 11 mkKV μ := by
  unfold kcomb
  rw [rowsXor_congr (r' := fun i => mkKV.getD i 0) μ fun i hi => by
    rw [kvec, tp_eq (by omega)]
    exact of_decide_eq_true kvec_chk i (List.mem_range.2 hi), rowsXor_eq]

@[expose] noncomputable def mkAllI (l : List Nat) (f : Nat → Nat → Bool) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun x _ ih i => andB (f i x) (ih (Nat.succ i))) l

theorem mkAllI_spec {f : Nat → Nat → Bool} : ∀ {l : List Nat} {i₀ : Nat}, mkAllI l f i₀ = true →
    ∀ i < l.length, f (i₀ + i) (l.getD i 0) = true
  | [], _, _ => by simp
  | x :: l, i₀, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    intro i hi
    rcases i with _ | i
    · exact h1
    · have := mkAllI_spec h2 i (by simpa using hi)
      have e : i₀ + (i + 1) = Nat.succ i₀ + i := by omega
      rw [List.getD_cons_succ, e]
      exact this

theorem foldl_set_ne (f : Nat → Nat) (c : Nat) : ∀ (L : List Nat) (a : Array Nat), (∀ ν ∈ L, f ν ≠ c) →
    (L.foldl (fun a μ => a.set! (f μ) μ) a)[c]? = a[c]?
  | [], _, _ => rfl
  | ν :: L, a, h => by
    rw [List.foldl_cons, foldl_set_ne f c L _ fun ν' hν' => h ν' (List.mem_cons_of_mem _ hν'),
      Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (h ν List.mem_cons_self)]

theorem foldl_set_size (f : Nat → Nat) : ∀ (L : List Nat) (a : Array Nat),
    (L.foldl (fun a μ => a.set! (f μ) μ) a).size = a.size
  | [], _ => rfl
  | ν :: L, a => by
    rw [List.foldl_cons, foldl_set_size f L, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem foldl_set_eq (f : Nat → Nat) (c μ : Nat) (hμ : f μ = c) : ∀ (L : List Nat) (a : Array Nat),
    μ ∈ L → (∀ ν ∈ L, f ν = c → ν = μ) → c < a.size →
    (L.foldl (fun a μ => a.set! (f μ) μ) a)[c]? = some μ
  | [], _, h, _, _ => absurd h (List.not_mem_nil)
  | ν :: L, a, hm, hu, hc => by
    rw [List.foldl_cons]
    by_cases hL : μ ∈ L
    · exact foldl_set_eq f c μ hμ L _ hL (fun ν' hν' => hu ν' (List.mem_cons_of_mem _ hν'))
        (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hc)
    · have hν : ν = μ := by
        rcases List.mem_cons.1 hm with h | h
        · exact h.symm
        · exact absurd h hL
      subst hν
      rw [foldl_set_ne f c L _ fun ν' hν' he => hL (hu ν' (List.mem_cons_of_mem _ hν') he ▸ hν'),
        Array.set!_eq_setIfInBounds, hμ, Array.getElem?_setIfInBounds_self_of_lt hc]

theorem kinvv_chk : mkAllI mkKINV (fun c v => actN 11 mkKV v == c && Nat.blt v 2048) 0 = true := by
  quickRfl

theorem kinj_chk : mkNodup ((List.range 2048).map (actN 11 mkKV)) = true := by quickRfl

theorem mkKINV_length : mkKINV.length = 2048 := by
  rw [← lenK_eq]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem kinv_getD {c : Nat} (hc : c < 2048) : kinv.getD c 0 = getN 0 mkKINV c := by
  have h := mkAllI_spec kinvv_chk c (mkKINV_length ▸ hc)
  rw [Nat.zero_add, Bool.and_eq_true, beq_iff_eq] at h
  have hlt := mkLt h.2
  have hinj := nodup_of_mkNodup kinj_chk
  unfold kinv
  simp only [kcomb_eq]
  rw [Array.getD_eq_getD_getElem?, foldl_set_eq (actN 11 mkKV) c _ h.1 _ _ (List.mem_range.2 hlt)
    (fun ν hν he => List.inj_on_of_nodup_map hinj hν (List.mem_range.2 hlt) (he.trans h.1.symm))
    (by simpa using hc), getN_zero_eq]
  rfl

end CertificateChecks.KernelJ4Q

end
