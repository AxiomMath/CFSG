module

public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.Quasithin.Vol2.KGFactG2RuInputs
import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelSporSch.G2Ru7164

open CFSG.Quasithin.H13.Ch4.G2Ru CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier CFSG.KC.Eval in
meta def g2Step (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let cj (t u : Array Nat) : Array Nat := compA 4060 (compA 4060 t u) (invCand 4060 t)
  let idxW (T : Array Nat) : Nat := ((List.range 64).find? fun e => eqA 4060 T g2WArr[e]!).getD 64
  let idxV (T : Array Nat) : Nat := ((List.range 8).find? fun e => eqA 4060 T g2VArr[e]!).getD 8
  let codeW (t : Array Nat) : Nat :=
    (List.range 6).foldr (fun k acc => acc * 64 + idxW (cj t g2WGenA[k]!)) 0
  let codeV (t : Array Nat) : Nat :=
    (List.range 3).foldr (fun k acc => acc * 8 + idxV (cj t g2VGenA[k]!)) 0
  let l (xs : List Nat) : Val := .list (xs.map Val.nat).toArray
  let pk (a : Array Nat) : Nat := a.foldr (fun x acc => (acc <<< 12) ||| x) 0
  .ok #[(`WL, l ((List.range 6).map fun k => pk g2WGenA[k]!)),
    (`VL, l ((List.range 3).map fun k => pk g2VGenA[k]!)),
    (`AL, l ((List.range 3).map fun i => pk (g2AA i))),
    (`WT, l ((List.range 64).map fun e => pk g2WArr[e]!)),
    (`VT, l ((List.range 8).map fun e => pk g2VArr[e]!)),
    (`CN, l ((List.range 2).map fun j => codeW (g2NA j))),
    (`CNV, l ((List.range 2).map fun j => codeV (g2NA j))),
    (`CC, l ((List.range 2).map fun j => codeW (g2CommA (g2NA j) g2XA))),
    (`CA, l ((List.range 3).map fun i => codeW (g2AA i))),
    (`CD, l ((List.range 3).map fun m => idxV (g2DA m)))]

end CertificateChecks.KernelSporSch.G2Ru7164

#kc_eval CertificateChecks.KernelSporSch.G2Ru7164 V CertificateChecks.KernelSporSch.G2Ru7164.g2Step

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.G2Ru7164

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSporSch.RuG
  CFSG.Quasithin.H13.Ch4.G2Ru

@[expose] noncomputable def pc (a b : Nat) : Nat := pcomp 4060 12 (mask 12) a b

@[expose] noncomputable def pinv (a : Nat) : Nat := pinvS 4060 12 (mask 12) a

@[expose] noncomputable def pid : Nat := pidn 4060 12

@[expose] noncomputable def letK (G : Nat → Nat) (l : Int) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pinv (G ((-l).toNat - 1))) (G (l.toNat - 1)) (decide (0 < l))

@[expose] noncomputable def wK (G : Nat → Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) pid (fun l _ ih => pc (letK G l) ih) w

@[expose] noncomputable def Cf (j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) C1 C0 (Nat.beq j 0)

@[expose] noncomputable def WG (k : Nat) : Nat := wK SG (g2WWords.getD k [])

@[expose] noncomputable def VG (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (wK SG (g2VWords.getD (k - 1) [])) (WG 0) (Nat.beq k 0)

@[expose] noncomputable def powK (t e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) pid (fun _ ih => pc t ih) e

@[expose] noncomputable def WPk (e : Nat) : Nat :=
  pc (powK (WG 0) (e % 2)) (pc (powK (WG 1) (e / 2 % 2)) (pc (powK (WG 2) (e / 4 % 2))
    (pc (powK (WG 3) (e / 8 % 2)) (pc (powK (WG 4) (e / 16 % 2)) (powK (WG 5) (e / 32 % 2))))))

@[expose] noncomputable def VPk (e : Nat) : Nat :=
  pc (powK (VG 0) (e % 2)) (pc (powK (VG 1) (e / 2 % 2)) (powK (VG 2) (e / 4 % 2)))

@[expose] noncomputable def inWK (T : Nat) : Bool := (List.range 64).any fun e => Nat.beq T (WPk e)

@[expose] noncomputable def inVK (T : Nat) : Bool := (List.range 8).any fun e => Nat.beq T (VPk e)

@[expose] noncomputable def conjK (t u : Nat) : Nat := pc (pc t u) (pinv t)

@[expose] noncomputable def normWK (t : Nat) : Bool := (List.range 6).all fun k => inWK (conjK t (WG k))
@[expose] noncomputable def normVK (t : Nat) : Bool := (List.range 3).all fun k => inVK (conjK t (VG k))
@[expose] noncomputable def centWK (t : Nat) : Bool :=
  (List.range 6).all fun k => Nat.beq (conjK t (WG k)) (WG k)
@[expose] noncomputable def centVK (t : Nat) : Bool :=
  (List.range 3).all fun k => Nat.beq (conjK t (VG k)) (VG k)
@[expose] noncomputable def sameWK (t u : Nat) : Bool :=
  (List.range 6).all fun k => Nat.beq (conjK t (WG k)) (conjK u (WG k))

@[expose] noncomputable def NAk (j : Nat) : Nat := wK Cf (g2NWords.getD j [])
@[expose] noncomputable def XAk : Nat := wK Cf g2XWord
@[expose] noncomputable def AAk (i : Nat) : Nat := wK Cf (g2AWords.getD i [])

@[expose] noncomputable def commK (t u : Nat) : Nat := pc (conjK t u) (pinv u)

@[expose] noncomputable def DAk (m : Nat) : Nat :=
  pc (VG (g2DIdx.getD m (0, 0)).2) (conjK (pinv (NAk (g2DIdx.getD m (0, 0)).1)) (VG (g2DIdx.getD m (0, 0)).2))

@[expose] noncomputable def DPk (e : Nat) : Nat :=
  pc (powK (DAk 0) (e % 2)) (pc (powK (DAk 1) (e / 2 % 2)) (powK (DAk 2) (e / 4 % 2)))
@[expose] noncomputable def APk (e : Nat) : Nat :=
  pc (powK (AAk 0) (e % 2)) (pc (powK (AAk 1) (e / 2 % 2)) (powK (AAk 2) (e / 4 % 2)))

theorem kPerm : bAnd(permOK 4060 12 (mask 12) (4060 * 12) C0 (pinv C0),
    bAnd(permOK 4060 12 (mask 12) (4060 * 12) C1 (pinv C1),
    (List.range 4).all fun j => permOK 4060 12 (mask 12) (4060 * 12) (SG j) (pinv (SG j)))) = true := by
  quickRfl

@[expose] noncomputable def WL (k : Nat) : Nat := V.WL.getD k 0
@[expose] noncomputable def VL (k : Nat) : Nat := V.VL.getD k 0
@[expose] noncomputable def AL (i : Nat) : Nat := V.AL.getD i 0
@[expose] noncomputable def WT (e : Nat) : Nat := V.WT.getD e 0
@[expose] noncomputable def VT (e : Nat) : Nat := V.VT.getD e 0

@[expose] noncomputable def WPL (e : Nat) : Nat :=
  pc (powK (WL 0) (e % 2)) (pc (powK (WL 1) (e / 2 % 2)) (pc (powK (WL 2) (e / 4 % 2))
    (pc (powK (WL 3) (e / 8 % 2)) (pc (powK (WL 4) (e / 16 % 2)) (powK (WL 5) (e / 32 % 2))))))
@[expose] noncomputable def VPL (e : Nat) : Nat :=
  pc (powK (VL 0) (e % 2)) (pc (powK (VL 1) (e / 2 % 2)) (powK (VL 2) (e / 4 % 2)))
@[expose] noncomputable def APL (e : Nat) : Nat :=
  pc (powK (AL 0) (e % 2)) (pc (powK (AL 1) (e / 2 % 2)) (powK (AL 2) (e / 4 % 2)))

@[expose] noncomputable def inWT (T : Nat) : Bool := (List.range 64).any fun e => Nat.beq T (WT e)
@[expose] noncomputable def inVT (T : Nat) : Bool := (List.range 8).any fun e => Nat.beq T (VT e)
@[expose] noncomputable def normWT (t : Nat) : Bool := (List.range 6).all fun k => inWT (conjK t (WL k))
@[expose] noncomputable def normVT (t : Nat) : Bool := (List.range 3).all fun k => inVT (conjK t (VL k))
@[expose] noncomputable def centWT (t : Nat) : Bool :=
  (List.range 6).all fun k => Nat.beq (conjK t (WL k)) (WL k)
@[expose] noncomputable def centVT (t : Nat) : Bool :=
  (List.range 3).all fun k => Nat.beq (conjK t (VL k)) (VL k)
@[expose] noncomputable def sameWT (t u : Nat) : Bool :=
  (List.range 6).all fun k => Nat.beq (conjK t (WL k)) (conjK u (WL k))

theorem kWL : (List.range 6).all (fun k => Nat.beq (WG k) (WL k)) = true := by quickRfl
theorem kVL : (List.range 3).all (fun k => Nat.beq (VG k) (VL k)) = true := by quickRfl
theorem kAL : (List.range 3).all (fun i => Nat.beq (AAk i) (AL i)) = true := by quickRfl
theorem kWT0 : (List.range 16).all (fun x => Nat.beq (WPL (x + 0)) (WT (x + 0))) = true := by quickRfl
theorem kWT1 : (List.range 16).all (fun x => Nat.beq (WPL (x + 16)) (WT (x + 16))) = true := by
  quickRfl
theorem kWT2 : (List.range 16).all (fun x => Nat.beq (WPL (x + 32)) (WT (x + 32))) = true := by
  quickRfl
theorem kWT3 : (List.range 16).all (fun x => Nat.beq (WPL (x + 48)) (WT (x + 48))) = true := by
  quickRfl
theorem kVT : (List.range 8).all (fun e => Nat.beq (VPL e) (VT e)) = true := by quickRfl

theorem eq_of_all {n : Nat} {f g : Nat → Nat} (h : (List.range n).all (fun k => Nat.beq (f k) (g k)) = true)
    {k : Nat} (hk : k < n) : f k = g k :=
  Nat.eq_of_beq_eq_true (List.all_eq_true.1 h k (List.mem_range.2 hk))

theorem all_congr' {n : Nat} {f g : Nat → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).all f = (List.range n).all g := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro H k hk
    rw [← h k (List.mem_range.1 hk)]
    exact H k hk
  · intro H k hk
    rw [h k (List.mem_range.1 hk)]
    exact H k hk

theorem any_congr' {n : Nat} {f g : Nat → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).any f = (List.range n).any g := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨k, hk, H⟩
    rw [h k (List.mem_range.1 hk)] at H
    exact ⟨k, hk, H⟩
  · rintro ⟨k, hk, H⟩
    rw [← h k (List.mem_range.1 hk)] at H
    exact ⟨k, hk, H⟩

theorem WG_eq {k : Nat} (hk : k < 6) : WG k = WL k := eq_of_all (f := WG) (g := WL) kWL hk
theorem VG_eq {k : Nat} (hk : k < 3) : VG k = VL k := eq_of_all (f := VG) (g := VL) kVL hk
theorem AAk_eq {i : Nat} (hi : i < 3) : AAk i = AL i := eq_of_all (f := AAk) (g := AL) kAL hi

theorem WT_eq {e : Nat} (he : e < 64) : WPL e = WT e := by
  have key : ∀ {b : Nat}, (List.range 16).all (fun x => Nat.beq (WPL (x + b)) (WT (x + b))) = true →
      b ≤ e → e < b + 16 → WPL e = WT e := by
    intro b h h1 h2
    have h3 := Nat.eq_of_beq_eq_true (List.all_eq_true.1 h (e - b) (List.mem_range.2 (by omega)))
    rwa [Nat.sub_add_cancel h1] at h3
  rcases (by omega : e < 16 ∨ (16 ≤ e ∧ e < 32) ∨ (32 ≤ e ∧ e < 48) ∨ 48 ≤ e) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · exact key (b := 0) kWT0 (by omega) (by omega)
  · exact key (b := 16) kWT1 h1 (by omega)
  · exact key (b := 32) kWT2 h1 (by omega)
  · exact key (b := 48) kWT3 h1 (by omega)

theorem WPk_eq {e : Nat} (he : e < 64) : WPk e = WT e := by
  unfold WPk
  rw [WG_eq (k := 0) (by norm_num), WG_eq (k := 1) (by norm_num), WG_eq (k := 2) (by norm_num),
    WG_eq (k := 3) (by norm_num), WG_eq (k := 4) (by norm_num), WG_eq (k := 5) (by norm_num)]
  exact WT_eq he

theorem VPk_eq {e : Nat} (he : e < 8) : VPk e = VT e := by
  unfold VPk
  rw [VG_eq (k := 0) (by norm_num), VG_eq (k := 1) (by norm_num), VG_eq (k := 2) (by norm_num)]
  exact eq_of_all (f := VPL) (g := VT) kVT he

theorem APk_eq (e : Nat) : APk e = APL e := by
  unfold APk APL
  rw [AAk_eq (i := 0) (by norm_num), AAk_eq (i := 1) (by norm_num), AAk_eq (i := 2) (by norm_num)]

theorem inWK_eq (T : Nat) : inWK T = inWT T := by
  unfold inWK inWT
  apply any_congr'
  intro e he
  rw [WPk_eq he]

theorem inVK_eq (T : Nat) : inVK T = inVT T := by
  unfold inVK inVT
  apply any_congr'
  intro e he
  rw [VPk_eq he]

theorem normWK_eq (t : Nat) : normWK t = normWT t := by
  unfold normWK normWT
  apply all_congr'
  intro k hk
  rw [WG_eq hk, inWK_eq]

theorem normVK_eq (t : Nat) : normVK t = normVT t := by
  unfold normVK normVT
  apply all_congr'
  intro k hk
  rw [VG_eq hk, inVK_eq]

theorem centWK_eq (t : Nat) : centWK t = centWT t := by
  unfold centWK centWT
  apply all_congr'
  intro k hk
  rw [WG_eq hk]

theorem centVK_eq (t : Nat) : centVK t = centVT t := by
  unfold centVK centVT
  apply all_congr'
  intro k hk
  rw [VG_eq hk]

theorem sameWK_eq (t u : Nat) : sameWK t u = sameWT t u := by
  unfold sameWK sameWT
  apply all_congr'
  intro k hk
  rw [WG_eq hk]

@[expose] noncomputable def nwE (t c : Nat) : Bool :=
  (List.range 6).all fun k => Nat.beq (conjK t (WL k)) (WT (c / 64 ^ k % 64))

@[expose] noncomputable def nvE (t c : Nat) : Bool :=
  (List.range 3).all fun k => Nat.beq (conjK t (VL k)) (VT (c / 8 ^ k % 8))

theorem normWK_of {t c : Nat} (h : nwE t c = true) : normWK t = true := by
  rw [normWK_eq]
  unfold nwE at h
  unfold normWT
  rw [List.all_eq_true] at h ⊢
  intro k hk
  exact List.any_eq_true.2 ⟨_, List.mem_range.2 (Nat.mod_lt _ (by norm_num)), h k hk⟩

theorem normVK_of {t c : Nat} (h : nvE t c = true) : normVK t = true := by
  rw [normVK_eq]
  unfold nvE at h
  unfold normVT
  rw [List.all_eq_true] at h ⊢
  intro k hk
  exact List.any_eq_true.2 ⟨_, List.mem_range.2 (Nat.mod_lt _ (by norm_num)), h k hk⟩

theorem sameWK_refl (t : Nat) : sameWK t t = true := by
  unfold sameWK
  rw [List.all_eq_true]
  intro k _
  exact Nat.beq_refl _

theorem sameWK_swap {t u : Nat} (h : sameWK t u = true) : sameWK u t = true := by
  unfold sameWK at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro k hk
  rw [Nat.eq_of_beq_eq_true (h k hk)]
  exact Nat.beq_refl _

theorem k1c : centVT XAk = true := by quickRfl

theorem k1 : centVK XAk = true := by
  rw [centVK_eq]
  exact k1c

theorem k2c : (!normWT XAk) = true := by quickRfl

theorem k2 : (!normWK XAk) = true := by
  rw [normWK_eq]
  exact k2c

theorem k3c : (List.range 2).all (fun j => nwE (NAk j) (V.CN.getD j 0) &&
    nvE (NAk j) (V.CNV.getD j 0) && nwE (commK (NAk j) XAk) (V.CC.getD j 0)) = true := by quickRfl

theorem k3 : (List.range 2).all (fun j => normWK (NAk j) && normVK (NAk j) &&
    normWK (commK (NAk j) XAk)) = true := by
  have h := k3c
  rw [List.all_eq_true] at h ⊢
  intro j hj
  have h1 := h j hj
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1 ⊢
  exact ⟨⟨normWK_of h1.1.1, normVK_of h1.1.2⟩, normWK_of h1.2⟩

theorem k4c : (List.range 3).all (fun m => decide (V.CD.getD m 0 < 8) &&
    Nat.beq (DAk m) (VT (V.CD.getD m 0))) = true := by quickRfl

theorem k4 : (List.range 3).all (fun m => inVK (DAk m)) = true := by
  have h := k4c
  rw [List.all_eq_true] at h ⊢
  intro m hm
  have h1 := h m hm
  rw [Bool.and_eq_true] at h1
  rw [inVK_eq]
  exact List.any_eq_true.2 ⟨_, List.mem_range.2 (of_decide_eq_true h1.1), h1.2⟩

theorem k5 : (List.range 8).all (fun i => (List.range 8).all fun j =>
    !decide (i < j) || !Nat.beq (DPk i) (DPk j)) = true := by quickRfl

theorem k6c : (List.range 3).all (fun i => nwE (AL i) (V.CA.getD i 0) && centVT (AL i) &&
    centWT (pc (AL i) (AL i))) = true := by quickRfl

theorem k6 : (List.range 3).all (fun i => normWK (AAk i) && centVK (AAk i) &&
    centWK (pc (AAk i) (AAk i))) = true := by
  have h := k6c
  rw [List.all_eq_true] at h ⊢
  intro i hi
  have h1 := h i hi
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1 ⊢
  rw [AAk_eq (List.mem_range.1 hi), centVK_eq, centWK_eq]
  exact ⟨⟨normWK_of h1.1.1, h1.1.2⟩, h1.2⟩

theorem k7c : (List.range 3).all (fun i => (List.range 3).all fun j =>
    !decide (i < j) || sameWT (pc (AL i) (AL j)) (pc (AL j) (AL i))) = true := by quickRfl

theorem k7 : (List.range 3).all (fun i => (List.range 3).all fun j =>
    sameWK (pc (AAk i) (AAk j)) (pc (AAk j) (AAk i))) = true := by
  have h := k7c
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt] at h ⊢
  intro i hi j hj
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · rcases h i hi j hj with h1 | h1
    · omega
    · rw [AAk_eq hi, AAk_eq hj, sameWK_eq]
      exact h1
  · exact sameWK_refl _
  · rcases h j hj i hi with h1 | h1
    · omega
    · apply sameWK_swap
      rw [AAk_eq hi, AAk_eq hj, sameWK_eq]
      exact h1

theorem k8c : (List.range 8).all (fun e => (List.range 8).all fun e' =>
    !decide (e < e') || !sameWT (APL e) (APL e')) = true := by quickRfl

theorem k8 : (List.range 8).all (fun e => (List.range 8).all fun e' =>
    !decide (e < e') || !sameWK (APk e) (APk e')) = true := by
  have h := k8c
  rw [List.all_eq_true] at h ⊢
  intro e he
  have h1 := h e he
  rw [List.all_eq_true] at h1 ⊢
  intro e' he'
  rw [APk_eq e, APk_eq e', sameWK_eq]
  exact h1 e' he'

theorem negc : ((!centWT XAk) && !inWT (NAk 0) && !Nat.beq (pc (AL 0) (AL 1)) (AL 1)) = true := by
  quickRfl

theorem neg : ((!centWK XAk) && !inWK (NAk 0) && !Nat.beq (pc (AAk 0) (AAk 1)) (AAk 1)) = true := by
  rw [centWK_eq, inWK_eq, AAk_eq (i := 0) (by norm_num), AAk_eq (i := 1) (by norm_num)]
  exact negc

end CertificateChecks.KernelSporSch.G2Ru7164

end
