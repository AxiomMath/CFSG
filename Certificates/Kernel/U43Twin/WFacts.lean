module

public import Certificates.Kernel.U43Twin.Facts
public import Certificates.Kernel.U43Twin.WPtsA
public import Certificates.Kernel.U43Twin.WPtsQ
public import Certificates.Kernel.U43Twin.WPtsP
public import Certificates.Kernel.U43Pk.CovFacts
public import CFSG.Certificates.Kernel.U43Twin.WSound
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.PackSetSound
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.U43Pk.Pts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Twin

open CFSG.KD.U43Pk CFSG.KD.U43Twin CFSG.KS.U43Pk CFSG.KS.U43Twin CFSG.KS.ArrBfsSim
open CFSG.Monster.B.Fischer CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open Certificates.U43Twin

#kc_forall_tree ch397503invAll (fun q => ch397503inv q = true) 2
  CertificateChecks.KernelU43Twin.ch397503inv

#kc_forall_tree ch397503sqAll (fun q => ch397503sq q = true) 16
  CertificateChecks.KernelU43Twin.ch397503sq

#kc_forall_tree ch397503sqpAll (fun q => ch397503sqp q = true) 3
  CertificateChecks.KernelU43Twin.ch397503sqp

#kc_forall_tree ch397503q8All (fun q => ch397503q8 q = true) 96
  CertificateChecks.KernelU43Twin.ch397503q8

#kc_forall_tree ch397503permAll (fun q => ch397503perm q = true) 36
  CertificateChecks.KernelU43Twin.ch397503perm

#kc_forall_tree ch397503centAll (fun q => ch397503cent q = true) 18
  CertificateChecks.KernelU43Twin.ch397503cent

#kc_forall_tree ch397503oddAll (fun q => ch397503odd q = true) 36
  CertificateChecks.KernelU43Twin.ch397503odd

theorem blk_of {f : ℕ → Bool} {w n : ℕ} (hw : 0 < w)
    (h : ∀ q < n, CFSG.KC.Enum.allBlk (Nat.mul w q) (fun i => CFSG.KC.Enum.strictB i f) w = true) :
    ∀ i < w * n, f i = true := by
  intro i hi
  have e := CFSG.KC.Pack.allBlk_spec (h (i / w) (Nat.div_lt_of_lt_mul hi)) (i % w)
    (Nat.mod_lt _ hw)
  rw [CFSG.KC.Pack.strictB_eq] at e
  have hi' : Nat.add (Nat.mul w (i / w)) (i % w) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod i w
  rwa [hi'] at e

theorem invAll : ∀ i < 128, invK TT FX IW T0K i = true :=
  blk_of (w := 64) (n := 2) (by norm_num) ch397503invAll

theorem sqAll : ∀ i < 1024, sqK KernelU43Pk.T SP R T0K i = true :=
  blk_of (w := 64) (n := 16) (by norm_num) ch397503sqAll

theorem sqpAll : ∀ k < 96, sqpK KernelU43Pk.T R SX (FX 35) T0K k = true :=
  blk_of (w := 32) (n := 3) (by norm_num) ch397503sqpAll

theorem permAll : ∀ i < 1152, permK CT PW EL (FX 37) (FX 40) i = true :=
  blk_of (w := 32) (n := 36) (by norm_num) ch397503permAll

theorem centAll : ∀ i < 1152, centK CT CW (FX 37) (FX 40) (FX 45) (FX 48) L1 L2 i = true :=
  blk_of (w := 64) (n := 18) (by norm_num) ch397503centAll

theorem oddAll : ∀ i < 1152, oddK CT DW GO i = true :=
  blk_of (w := 32) (n := 36) (by norm_num) ch397503oddAll

theorem q8All : ∀ k < 96, ∀ l < 96,
    q8pK KernelU43Pk.T R SX EL (QW (Nat.add (Nat.mul 96 k) l)) k l = true := by
  intro k hk l hl
  have e := CFSG.KC.Pack.allBlk_spec (ch397503q8All k hk) l hl
  have e0 : Nat.add 0 l = l := Nat.zero_add l
  rw [e0, CFSG.KC.Pack.strictB_eq] at e
  exact e

theorem fxDigK : ∀ i < 100, digK (FX i) = true := by decide +kernel

theorem fxDig {i : ℕ} (hi : i < 100) : Dig (FX i) := digK_spec (fxDigK i hi)

theorem invPin : invCands.toList = (List.range 35).map fun w => dec (FX w) := by decide +kernel

theorem candsPin : q8Cands.toList = [dec (FX 35)] := by decide +kernel

theorem P1Eq : P1 = dec (FX 37) := by decide +kernel

theorem Q1Eq : Q1 = dec (FX 40) := by decide +kernel

theorem P2Eq : P2 = dec (FX 45) := by decide +kernel

theorem Q2Eq : Q2 = dec (FX 48) := by decide +kernel

theorem ELpin : ∀ s < 2, EL s 0 = IDK ∧ EL s 2 = powK (EL s 1) 2 ∧ EL s 3 = powK (EL s 1) 3 ∧
    EL s 5 = mulK (EL s 4) (EL s 1) ∧ EL s 6 = mulK (EL s 4) (powK (EL s 1) 2) ∧
    EL s 7 = mulK (EL s 4) (powK (EL s 1) 3) := by decide +kernel

theorem ELfx : EL 0 1 = FX 37 ∧ EL 0 4 = FX 40 ∧ EL 1 1 = FX 45 ∧ EL 1 4 = FX 48 := by
  decide +kernel

theorem ELlt {s u : ℕ} (hs : s < 2) (hu : u < 8) : Nat.add 36 (Nat.add (Nat.mul 8 s) u) < 100 := by
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem ELdig {s u : ℕ} (hs : s < 2) (hu : u < 8) : Dig (EL s u) := fxDig (ELlt hs hu)

theorem ELmem {s : ℕ} (hs : s < 2) {P Q : ℕ} (hP : EL s 1 = P) (hQ : EL s 4 = Q) :
    ∀ u < 8, Dig (EL s u) ∧ dec (EL s u) ∈ q8Elts (dec P) (dec Q) := by
  intro u hu
  refine ⟨ELdig hs hu, ?_⟩
  obtain ⟨e0, e2, e3, e5, e6, e7⟩ := ELpin s hs
  rw [← hP, ← hQ, q8Elts_dec (ELdig hs (by norm_num)) (ELdig hs (by norm_num))]
  interval_cases u <;>
    simp only [e0, e2, e3, e5, e6, e7, List.mem_cons, true_or, or_true]

theorem E1mem : ∀ u < 8, Dig (EL 0 u) ∧ dec (EL 0 u) ∈ q8Elts P1 Q1 := by
  rw [P1Eq, Q1Eq]
  exact ELmem (by norm_num) ELfx.1 ELfx.2.1

theorem E2mem : ∀ u < 8, Dig (EL 1 u) ∧ dec (EL 1 u) ∈ q8Elts P2 Q2 := by
  rw [P2Eq, Q2Eq]
  exact ELmem (by norm_num) ELfx.2.2.1 ELfx.2.2.2

theorem GOpin : ∀ g < 8, GO g = EL 0 g ∧ GO (Nat.add 8 g) = EL 1 g := by decide +kernel

theorem Gmem : ∀ g < 16, Dig (GO g) ∧ dec (GO g) ∈ q8Elts P1 Q1 ++ q8Elts P2 Q2 := by
  intro g hg
  by_cases h8 : g < 8
  · rw [(GOpin g h8).1]
    obtain ⟨d, m⟩ := E1mem g h8
    exact ⟨d, List.mem_append_left _ m⟩
  · have e : g = Nat.add 8 (g - 8) := by
      rw [Nat.add_eq]
      omega
    rw [e, (GOpin (g - 8) (by omega)).2]
    obtain ⟨d, m⟩ := E2mem (g - 8) (by omega)
    exact ⟨d, List.mem_append_right _ m⟩

theorem psiPin : slQuads.map (fun m => psiTab[qidx m]!) = (List.range 24).map fun v => dec (L2 v) := by
  decide +kernel

theorem h2Pin : H2tab.toList = (List.range 24).map fun v => dec (L1 v) := by decide +kernel

theorem L2mem : ∀ v < 24, Dig (L2 v) ∧ dec (L2 v) ∈ slQuads.map fun m => psiTab[qidx m]! := by
  intro v hv
  refine ⟨fxDig (i := Nat.add 52 v) (by rw [Nat.add_eq]; omega), ?_⟩
  rw [psiPin]
  exact List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩

theorem L1mem : ∀ v < 24, Dig (L1 v) ∧ dec (L1 v) ∈ H2tab.toList := by
  intro v hv
  refine ⟨fxDig (i := Nat.add 76 v) (by rw [Nat.add_eq]; omega), ?_⟩
  rw [h2Pin]
  exact List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩

theorem tCert_eq : tCert () = cert 3 128 (fun i => dec (TT i)) TE TPA TLA := by
  have hsz : gT.size = 3 := rfl
  obtain ⟨Tb, -, h0⟩ := tables_of (n := 3) (N := 128) (by norm_num) gTEq gTV tAll
  unfold tCert
  rw [hsz, ← h0]
  exact arrBfs_eq Tb (by norm_num)

theorem cCert_eq : cCert () = cert 2 1152 (fun i => dec (CT i)) CE CPA CLA := by
  have hsz : gC.size = 2 := rfl
  obtain ⟨Tb, -, h0⟩ := tables_of (n := 2) (N := 1152) (by norm_num) gCEq gCV cAll
  unfold cCert
  rw [hsz, ← h0]
  exact arrBfs_eq Tb (by norm_num)

theorem rawTT {i : ℕ} (hi : i < 128) : rawValidK (TT i) = true :=
  (validK_spec (ptK_spec (tAll i hi)).1).1

theorem rawCT {i : ℕ} (hi : i < 1152) : rawValidK (CT i) = true :=
  (validK_spec (ptK_spec (cAll i hi)).1).1

theorem invOK_true : invOK () = true := by
  unfold invOK
  rw [tCert_eq]
  dsimp only
  rw [cert_pts_size]
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  rw [cert_pts_get hi]
  exact invK_spec invPin T0Eq T0Dig (rawTT hi) (invAll i hi)

theorem q8OK_true : q8OK () = true := by
  unfold q8OK
  rw [KernelU43Pk.bfs_eq]
  dsimp only
  rw [cert_pts_size]
  simp only [List.all_eq_true, List.mem_filter, List.mem_range, and_imp]
  intro i hi hsi j hj hsj
  rw [cert_pts_get hi] at hsi ⊢
  rw [cert_pts_get hj] at hsj ⊢
  rw [T0Eq] at hsi hsj
  obtain ⟨k, hk, rfl⟩ := sqK_spec (KernelU43Pk.digT hi) T0Dig (sqAll _ hi) hsi
  obtain ⟨l, hl, rfl⟩ := sqK_spec (KernelU43Pk.digT hj) T0Dig (sqAll _ hj) hsj
  rw [candsPin]
  exact q8pK_spec (KernelU43Pk.rawT hi) (KernelU43Pk.rawT hj) (sqpAll k hk) (sqpAll l hl) T0Eq T0Dig
    (List.mem_singleton_self _) rfl (fxDig (by norm_num)) E1mem E2mem (q8All k hk l hl)

theorem permOK_true : permOK () = true := by
  unfold permOK
  rw [cCert_eq]
  dsimp only
  rw [cert_pts_size]
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  have hE1 := E1mem
  rw [cert_pts_get hi]
  rw [P1Eq, Q1Eq] at hE1 ⊢
  exact permK_spec (rawCT hi) (fxDig (by norm_num)) (fxDig (by norm_num)) hE1 E2mem (permAll i hi)

theorem oddOK_true : oddOK () = true := by
  unfold oddOK
  rw [cCert_eq]
  dsimp only
  rw [cert_pts_size]
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  rw [cert_pts_get hi]
  exact oddK_spec (rawCT hi) Gmem (oddAll i hi)

theorem centOK_true : centOK () = true := by
  unfold centOK
  rw [cCert_eq]
  dsimp only
  rw [cert_pts_size]
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  rw [cert_pts_get hi, P1Eq, Q1Eq, P2Eq, Q2Eq]
  have h := centAll i hi
  unfold centK at h
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := bAnd_spec h
  have hd := (rawValidK_spec (rawCT hi)).2.1
  rw [halfK_spec hd (fxDig (by norm_num)) (fxDig (by norm_num)) L2mem h1,
    halfK_spec hd (fxDig (by norm_num)) (fxDig (by norm_num)) L1mem h2, Bool.and_self]

end CertificateChecks.KernelU43Twin

end
