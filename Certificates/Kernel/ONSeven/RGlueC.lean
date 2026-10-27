module

public import Certificates.Kernel.ONSeven.RGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.ONR CFSG.KS.ONOrb CFSG.KC.B3S3K
  CFSG.RankThree.Native CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
open CertificateChecks.KernelSpor.ONS (WW letOK letM_of lets_all getD_mem arr_get WW_lt
  pcomp_get peq_of_onP lin_WW)
open CertificateChecks.KernelSpor.ON8 (onP)

@[expose] def cAll (r : Nat) : Array (Array Nat) :=
  (onSevenCArrs r).push (onSevenRepArr r) ++ (if r < 3 then onSevenFArrs r else #[])

theorem cAll_get {r : Nat} (hr : r < 5) :
    ∀ s < (cAll r).size, ∀ x < 245520, ((cAll r)[s]!)[x]! = cF r s x := by
  intro s hs x hx
  unfold cAll at hs ⊢
  rw [cAll_eq hr] at hs ⊢
  rw [Array.size_map] at hs
  exact words_get (cWords_ok hr) hs hx

theorem cAll_size_ge {r : Nat} : (onSevenCArrs r).size + 1 ≤ (cAll r).size := by
  unfold cAll
  simp

theorem cRes {r N w k : Nat} {T G D S : Nat → Nat} (hr5 : r < 5) (hk : (onSevenCArrs r).size = k)
    (ho : orbK N w k T G D S = true)
    (hres : ∀ s < (cAll r).size, resK N w T (cF r s) (G s) = true) :
    onSevenCR r = (Array.ofFn (n := N) fun i => T i.val) ∧
      onSevenResOK (Array.ofFn (n := N) fun i => T i.val)
        ((onSevenCArrs r).push (onSevenRepArr r)) = true ∧
      BindA N w ((onSevenCArrs r).map (onSevenTab (Array.ofFn (n := N) fun i => T i.val))) k G ∧
      onSevenTab (Array.ofFn (n := N) fun i => T i.val) (onSevenRepArr r) = unpack N w (G k) := by
  have hA := cAll_get hr5
  have hP := prefix_get (rest := if r < 3 then onSevenFArrs r else #[]) hA
  obtain ⟨hcs, hx⟩ := push_get hP
  have hsz := cAll_size_ge (r := r)
  have O := orbK_spec ho
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold onSevenCR
    exact onSevenOrbit_eq (orec_of hk (fun s hs => hcs s (by omega)) ho
      (fun s hs => hres s (by omega)))
  · exact resOK_of ho hP (fun s hs => hres s (by simp at hs; omega))
  · have := bind_of ho hcs (fun s hs => hres s (by omega))
    rwa [hk] at this
  · rw [← hk]
    exact tab_eq hx O.lt O.inj (hres _ (by omega))

theorem fRes {r N w k : Nat} {T G D S : Nat → Nat} (hr3 : r < 3) (hk : (onSevenCArrs r).size = k)
    (ho : orbK N w k T G D S = true)
    (hres : ∀ s < (cAll r).size, resK N w T (cF r s) (G s) = true) :
    onSevenResOK (Array.ofFn (n := N) fun i => T i.val) (onSevenFArrs r) = true ∧
      BindA N w ((onSevenFArrs r).map (onSevenTab (Array.ofFn (n := N) fun i => T i.val)))
        (onSevenFArrs r).size fun l => G (k + 1 + l) := by
  have hA := cAll_get (r := r) (by omega)
  have hS := suffix_get hA
  have e : (if r < 3 then onSevenFArrs r else #[]) = onSevenFArrs r := if_pos hr3
  rw [e] at hS
  have hsz : ((onSevenCArrs r).push (onSevenRepArr r)).size = k + 1 := by simp [hk]
  rw [hsz] at hS
  have hres' : ∀ l < (onSevenFArrs r).size, resK N w T (cF r (k + 1 + l)) (G (k + 1 + l)) = true :=
    fun l hl => hres _ (by unfold cAll; rw [e]; simp; omega)
  exact ⟨resOK_of (GR := fun l => G (k + 1 + l)) ho hS hres', bind_of ho hS hres'⟩

theorem comm_of {r : Nat} (hr5 : r < 5)
    (h : ∀ k < (onSevenCArrs r).size, onP (fun y => cF r k (cF r (onSevenCArrs r).size y))
      (fun y => cF r (onSevenCArrs r).size (cF r k y)) = true) :
    ∀ k < (onSevenCArrs r).size,
      peq nPts (pcomp nPts (onSevenCArrs r)[k]! (onSevenRepArr r))
        (pcomp nPts (onSevenRepArr r) (onSevenCArrs r)[k]!) = true := by
  have hA := cAll_get hr5
  have hP := prefix_get (rest := if r < 3 then onSevenFArrs r else #[]) hA
  obtain ⟨hcs, hx⟩ := push_get hP
  have hsz := cAll_size_ge (r := r)
  have hl : ∀ s < (cAll r).size, CertificateChecks.KernelSpor.ON3.LetM 7 ((cWords r).getD s []) :=
    fun s hs => letM_of (lets_all (cWords_ok hr5) (getD_mem [] (by
      unfold cAll at hs
      rw [cAll_eq hr5, Array.size_map] at hs
      exact hs)))
  have hlt : ∀ {s : Nat} (y : Nat), y < 245520 → cF r s y < 245520 := fun _ hy => WW_lt hy
  intro k hk
  have lk := lin_WW (hl k (by omega))
  have lx := lin_WW (hl (onSevenCArrs r).size (by omega))
  exact peq_of_onP (CFSG.KS.ONLin.Lin.comp lk lx) (CFSG.KS.ONLin.Lin.comp lx lk)
    (fun i hi => by
      rw [pcomp_get hi, hx i hi, hcs k hk _ (hlt _ hi)]
      rfl)
    (fun i hi => by
      rw [pcomp_get hi, hcs k hk i hi, hx _ (hlt _ hi)]
      rfl)
    (h k hk)

end CertificateChecks.KernelSpor.ONR

end
