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

theorem wC1080 : wC 1080 = 11 := by decide

theorem wC243 : wC 243 = 8 := by decide

@[expose] noncomputable def ucv (hY : Ly1080.YOK) (k : Nat) : CV 1080 :=
  if hk : k < 4 then
    cvOf (UH.F k) (Ly1080.ug k)
      (by
        rw [wC1080]
        exact Nat.eq_of_beq_eq_true (allN_spec k_canon.1 k hk))
      (fun i hi => by rw [wC1080]; exact ug_pg hY hk hi)
  else 1

theorem ucv_val (hY : Ly1080.YOK) {k : Nat} (hk : k < 4) : (ucv hY k).1 = UH.F k := by
  unfold ucv
  rw [dif_pos hk]
  rfl

theorem ev_ucv (hY : Ly1080.YOK) {k : Nat} (hk : k < 4) : ev (ucv hY k) = Ly1080.ug k := by
  unfold ucv
  rw [dif_pos hk, ev_cvOf]

@[expose] noncomputable def gcv (hT : Ly243.trCheck = true) (k : Nat) : CV 243 :=
  if hk : k < 5 then
    cvOf (GH.F k) (Ly243.gg k)
      (by
        rw [wC243]
        exact Nat.eq_of_beq_eq_true (allN_spec k_canon.2.1 k hk))
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
        exact Nat.eq_of_beq_eq_true (allN_spec k_canon.2.2 k hk))
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

theorem letT_eq {n : Nat} [Small n] {T TI : Nat → Nat} {u : Nat → CV n} {m : Nat}
    (hT : ∀ k < m, T k = (u k).1) (hTI : ∀ k < m, TI k = pinvS n (wC n) (mask (wC n)) (u k).1)
    {l : Int} (hl : l ≠ 0 ∧ l.natAbs ≤ m) : letT T TI l = (wordLetter u l).1 := by
  unfold wordLetter
  cases l with
  | ofNat k =>
    have h1 : k ≠ 0 := fun e => hl.1 (by rw [e]; rfl)
    have h2 : k ≤ m := hl.2
    have hk : 0 < (Int.ofNat k) := by
      rw [Int.ofNat_eq_coe]
      omega
    rw [if_pos hk]
    change T (k - 1) = (u ((Int.ofNat k).toNat - 1)).1
    rw [hT _ (by omega)]
    rfl
  | negSucc k =>
    have h2 : k + 1 ≤ m := hl.2
    have hk : ¬ 0 < Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [if_neg hk]
    change TI k = ((u ((-Int.negSucc k).toNat - 1))⁻¹).1
    have e : (-Int.negSucc k).toNat - 1 = k := by
      rw [Int.negSucc_eq]
      omega
    rw [e, hTI _ (by omega)]
    rfl

theorem uWord1080_eq (hY : Ly1080.YOK) {ws : List Int}
    (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 4) :
    uWord1080 ws = (wordC (wordLetter (ucv hY)) ws).1 := by
  unfold uWord1080
  rw [← wC1080]
  exact wprod_eq _ ws fun l hl => letT_eq (m := 4) (fun k hk => (ucv_val hY hk).symm)
    (fun k hk => by rw [ucv_val hY hk, wC1080]; rfl) (hws l hl)

theorem ghWord_eq (hT : Ly243.trCheck = true) {ws : List Int}
    (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 5) :
    wprod 243 8 (mask 8) (letT GH.F ghInv) ws = (wordC (wordLetter (gcv hT)) ws).1 := by
  rw [← wC243]
  exact wprod_eq _ ws fun l hl => letT_eq (m := 5) (fun k hk => (gcv_val hT hk).symm)
    (fun k hk => by rw [gcv_val hT hk, wC243]; rfl) (hws l hl)

theorem ev_wordC_letter {n : Nat} [Small n] (u : Nat → CV n) (g : Nat → Perm (Fin n)) {m : Nat}
    (hu : ∀ k < m, ev (u k) = g k) {ws : List Int} (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ m) :
    ev (wordC (wordLetter u) ws) = CFSG.Sporadic.Th.wordG (wordLetter g) ws := by
  rw [ev_wordC]
  unfold CFSG.Sporadic.Th.wordG
  congr 1
  refine List.map_congr_left fun l hl => ?_
  have h := hws l hl
  unfold wordLetter
  split_ifs with hp
  · exact hu _ (by omega)
  · rw [ev_inv, hu _ (by omega)]

end CertificateChecks.KernelLy

end
