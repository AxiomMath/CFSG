module

public import CFSG.Certificates.Kernel.LyGlue.WordSound
public import CFSG.Sporadic.Recognition.LyonsAmalgam
public import Certificates.Kernel.LyGlue.Facts1
public import Certificates.Kernel.LyGlue.KPt

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV

section

variable {n : Nat} [hs : Small n]

@[expose] noncomputable def cvOf (p : Nat) (g : Perm (Fin n)) (hshr : p >>> (n * wC n) = 0)
    (hpg : ∀ i (hi : i < n), pg (wC n) (mask (wC n)) p i = (g ⟨i, hi⟩ : Nat)) : CV n :=
  ⟨p, hshr, fun i hi => by rw [hpg i hi]; exact (g _).2, fun a ha b hb e => by
    rw [hpg a ha, hpg b hb] at e
    exact congrArg Fin.val (g.injective (Fin.ext e))⟩

theorem ev_cvOf (p : Nat) (g : Perm (Fin n)) (hshr) (hpg) : ev (cvOf p g hshr hpg) = g := by
  ext i
  rw [ev_apply]
  exact hpg i i.2

theorem cvOf_val (p : Nat) (g : Perm (Fin n)) (hshr) (hpg) : (cvOf p g hshr hpg).1 = p := rfl

theorem cv_eq_of_ev {a b : CV n} (h : ev a = ev b) : a = b := ev_injective h

end

theorem wC243 : wC 243 = 8 := by decide

@[expose] noncomputable def gcv (hT : Ly243.trCheck = true) (k : Nat) : CV 243 :=
  if hk : k < 5 then
    cvOf (GH.F k) (Ly243.gg k)
      (by
        rw [wC243]
        exact Nat.eq_of_beq_eq_true (allN_spec k_canon.1 k hk))
      (fun i hi => by rw [wC243]; exact gg_pg hT hk hi)
  else 1

theorem gcv_val (hT : Ly243.trCheck = true) {k : Nat} (hk : k < 5) : (gcv hT k).1 = GH.F k := by
  unfold gcv
  rw [dif_pos hk]
  rfl

theorem ev_gcv (hT : Ly243.trCheck = true) {k : Nat} (hk : k < 5) : ev (gcv hT k) = Ly243.gg k := by
  unfold gcv
  rw [dif_pos hk, ev_cvOf]

@[expose] noncomputable def lcv (hT : Ly243.trCheck = true) (k : Nat) : CV 243 :=
  if hk : k < 3 then
    cvOf (LH.F k) (Ly243.lineG k)
      (by
        rw [wC243]
        exact Nat.eq_of_beq_eq_true (allN_spec k_canon.2 k hk))
      (fun i hi => by rw [wC243]; exact lineG_pg hT hk hi)
  else 1

theorem lcv_val (hT : Ly243.trCheck = true) {k : Nat} (hk : k < 3) : (lcv hT k).1 = LH.F k := by
  unfold lcv
  rw [dif_pos hk]
  rfl

theorem ev_lcv (hT : Ly243.trCheck = true) {k : Nat} (hk : k < 3) :
    ev (lcv hT k) = Ly243.lineG k := by
  unfold lcv
  rw [dif_pos hk, ev_cvOf]

end CertificateChecks.KernelLy

end
