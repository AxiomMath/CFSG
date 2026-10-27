module

public import Certificates.Kernel.Misc.Perm.HS100.S0Checks
public import Certificates.Kernel.Misc.Perm.HS100.CliqueGlue

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.S0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.KC.PermAdj
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0 CFSG.KC.Misc.HexFlat
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB conj_unpack' memK fixK)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of commA_F ppow_canon ppow_succ
  any_mem card_filter_fin keyInj)
open CFSG.KLie.CT (fget)

theorem tab_eq (k : ℕ) (hk : k < 11) : tab k = unpack 100 7 (SX.F k) := by
  rw [tab, SX.eq]
  exact hexTable3_sound SX.all k hk

theorem z0_eq : z0 = unpack 100 7 Z0 := by
  rw [z0, s5Z, s5Tab, ZX.eq]
  exact hexTable3_sound ZX.all 4 (by norm_num)

theorem e0_get : ∀ k < 4, zasE0Gens[k]! = unpack 100 7 (EX.F k) := by
  intro k hk
  rw [zasE0Gens, zasEGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn,
    show 4 * 0 + k = k by omega, EX.eq]
  exact hexTable3_sound EX.all k hk

theorem ppS {k : ℕ} (hk : k < 11) : PP 100 7 (SX.F k) := pp_of_permB sz (allN_spec sperm k hk)

theorem cS {k : ℕ} (hk : k < 11) : canonK 100 7 (mask 7) (100 * 7) (SX.F k) = true := (ppS hk).1

theorem validS {k : ℕ} (hk : k < 11) : validA 100 (unpack 100 7 (SX.F k)) = true :=
  validA_unpack (allN_spec sperm k hk)

theorem inS {k : ℕ} (hk : k < 11) : s5InP (unpack 100 7 (SX.F k)) = true :=
  s5InP_unpack (allN_spec (and_of ssift).1 k hk)

theorem ppZ : PP 100 7 Z0 := pp_of_permB sz (and_of zperm).1

theorem keysOK : ∀ p ∈ keys, p < 100 := by decide

theorem pw_unpack {p : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) :
    ∀ e, pw (unpack 100 7 p) e = unpack 100 7 (ppow 100 7 (mask 7) (pidn 100 7) p e)
  | 0 => hidA
  | e + 1 => by
    rw [pw, pw_unpack hp e, compA_unpack hp (ppow_canon hp e), ppow_succ]

theorem nums' : KK.ng = 4 ∧ KK.N = 120 ∧ CY.ng = 5 ∧ CY.N = 360 ∧ AB.ng = 6 ∧ AB.N = 1440 ∧
    CB.ng = 7 ∧ CB.N = 2880 ∧ JJ.ng = 4 ∧ JJ.N = 360 ∧ E0.ng = 4 ∧ E0.N = 16 ∧ ZO.ng = 2 ∧
    ZO.N = 5775 ∧ UO.ng = 2 ∧ UO.N = 15400 ∧ ZO.r0 = 0 ∧ UO.r0 = 0 := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  tauto

theorem binds' : (∀ k < 4, KK.G k = SX.F (Nat.add 1 k)) ∧ (∀ k < 5, CY.G k = SX.F k) ∧
    (∀ k < 6, AB.G k = SX.F (Nat.add 5 k)) ∧ CB.G 0 = SX.F 1 ∧
    (∀ k < 6, CB.G (Nat.succ k) = SX.F (Nat.add 5 k)) ∧
    (∀ k < 4, JJ.G k = pcomp 100 7 (mask 7) (SX.F (Nat.add 5 k)) (SX.F (Nat.add 6 k))) ∧
    (∀ k < 4, E0.G k = EX.F k) ∧ (∀ k < 2, ZO.G k = HX.F k) ∧ (∀ k < 2, UO.G k = HX.F k) ∧
    ZO.T ZO.r0 = Z0 ∧ UO.T UO.r0 = U0 ∧ K3.T K3.r1 = Y0 := by
  have h := binds
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨fun k hk => Nat.eq_of_beq_eq_true (allN_spec h1 k hk),
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h2 k hk),
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h3 k hk), h4,
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h5 k hk),
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h6 k hk),
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h7 k hk),
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h8 k hk),
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h9 k hk), h10, h11, h12⟩

theorem prods' : Nat.beq (pcomp 100 7 (mask 7) Z0 Z0) (pidn 100 7) = true ∧
    Nat.beq Z0 (pidn 100 7) = false ∧ Nat.beq U0 (pidn 100 7) = false ∧
    Nat.beq (ppow 100 7 (mask 7) (pidn 100 7) Y0 3) (pidn 100 7) = true ∧
    Nat.beq Y0 (pidn 100 7) = false ∧ cK Y0 Z0 = true ∧
    Nat.beq (pcomp 100 7 (mask 7) (SX.F 1) (SX.F 2)) (pidn 100 7) = false ∧
    Nat.beq (pcomp 100 7 (mask 7) (SX.F 5) (SX.F 6)) (pidn 100 7) = false ∧
    (∀ k < 4, cK Y0 (SX.F (Nat.add 1 k)) = true) ∧ (∀ k < 6, cK U0 (SX.F (Nat.add 5 k)) = true) ∧
    fixK 100 7 Z0 = 20 ∧ fixK 100 7 U0 = 0 := by
  have h := prods
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, h6, ?_, ?_, fun k hk => allN_spec h9 k hk,
    fun k hk => allN_spec h10 k hk, h11, h12⟩ <;> simp_all

theorem y0_eq : y0 = unpack 100 7 Y0 := tab_eq 0 (by norm_num)

theorem u0_eq : u0 = unpack 100 7 U0 := tab_eq 1 (by norm_num)

theorem cK_eq {p q : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true)
    (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    commA 100 (unpack 100 7 p) (unpack 100 7 q) = cK p q := commA_F hp hq

theorem c4 : ∀ k < 4, Nat.add 1 k < 11 := fun k hk => by simp only [Nat.add_eq]; omega

theorem c6 : ∀ k < 6, Nat.add 5 k < 11 := fun k hk => by simp only [Nat.add_eq]; omega

theorem xGens_get : ∀ k < 4, xGens[k]! = unpack 100 7 (SX.F (Nat.add 1 k)) := by
  intro k hk
  interval_cases k <;> exact tab_eq _ (by norm_num)

theorem rGens_get : ∀ k < 5, rGens[k]! = unpack 100 7 (SX.F (Nat.add 5 k)) := by
  intro k hk
  interval_cases k <;> exact tab_eq _ (by norm_num)

theorem aGens_get : ∀ k < 6, aGens[k]! = unpack 100 7 (SX.F (Nat.add 5 k)) := by
  intro k hk
  interval_cases k <;> exact tab_eq _ (by norm_num)

theorem pGens_get : ∀ k < 2, pGens[k]! = unpack 100 7 (HX.F k) := by
  intro k hk
  interval_cases k
  · exact hs100Arr_eq 0 (by norm_num)
  · exact hs100Arr_eq 1 (by norm_num)

theorem basicOK_true : basicOK = true := by
  unfold basicOK
  have p1 : allLt pGens.size (fun k => validA 100 pGens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk2 : k < 2 := hk
    rw [pGens_get k hk2]
    exact validA_unpack (allN_spec CertificateChecks.KernelMisc.HS100.Five.hperm k hk2)
  have p2 : allLt xGens.size (fun k => validA 100 xGens[k]! && s5InP xGens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk4 : k < 4 := hk
    rw [xGens_get k hk4, validS (c4 k hk4), inS (c4 k hk4)]
    rfl
  have p3 : allLt rGens.size (fun k => validA 100 rGens[k]! && s5InP rGens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk5 : k < 5 := hk
    rw [rGens_get k hk5, validS (c6 k (by omega)), inS (c6 k (by omega))]
    rfl
  have z1 : validA 100 z0 = true := by rw [z0_eq]; exact validA_unpack (and_of zperm).1
  have z2 : s5InP z0 = true := by rw [z0_eq]; exact s5InP_unpack (and_of ssift).2
  have z3 : eqA 100 (compA 100 z0 z0) (idA 100) = true := by
    rw [z0_eq, compA_unpack ppZ.1 ppZ.1, hidA, eqA_F (canonK_pcomp ppZ.1 ppZ.1) pidPP.1]
    exact prods'.1
  have z4 : (!eqA 100 z0 (idA 100)) = true := by
    rw [z0_eq, hidA, eqA_F ppZ.1 pidPP.1, prods'.2.1]
    rfl
  have u4 : (!eqA 100 u0 (idA 100)) = true := by
    rw [u0_eq, hidA, eqA_F (p := U0) (cS (k := 1) (by norm_num)) pidPP.1, prods'.2.2.1]
    rfl
  have y1 : validA 100 y0 = true := by rw [y0_eq]; exact validS (by norm_num)
  have y2 : s5InP y0 = true := by rw [y0_eq]; exact inS (by norm_num)
  have e1 : validA 100 pEl = true := by rw [pEl, tab_eq 10 (by norm_num)]; exact validS (by norm_num)
  have e2 : s5InP pEl = true := by rw [pEl, tab_eq 10 (by norm_num)]; exact inS (by norm_num)
  rw [p1, z1, z2, z3, z4, y1, y2, u4, p2, p3, e1, e2]
  rfl

theorem countFix (p : ℕ) : ∀ m, m ≤ 100 →
    (List.range m).countP (fun i => (unpack 100 7 p)[i]! == i) =
      Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => ℕ) 0 1
        (Nat.beq (pg 7 (mask 7) p i) i))) m
  | 0, _ => rfl
  | m + 1, h => by
    rw [List.range_succ, List.countP_append, countFix p m (by omega), List.countP_singleton,
      unpack_get' (by omega : m < 100)]
    change _ = Nat.add _ _
    cases hb : Nat.beq (pg 7 (mask 7) p m) m
    · have : (pg 7 (mask 7) p m == m) = false := by
        rw [beq_eq_false_iff_ne]; exact fun e => by rw [e, Nat.beq_refl] at hb; cases hb
      simp [this]
    · have : (pg 7 (mask 7) p m == m) = true := by
        rw [beq_iff_eq]; exact Nat.eq_of_beq_eq_true hb
      simp [this]

theorem fixCnt_eq (p : ℕ) : fixCnt (unpack 100 7 p) = fixK 100 7 p := by
  unfold fixCnt
  have e := card_filter_fin 100 (fun i => (unpack 100 7 p)[i]! == i)
  have hf : (Finset.univ.filter fun i : Fin 100 => (unpack 100 7 p)[i.1]! = i.1) =
      Finset.univ.filter fun i : Fin 100 => ((unpack 100 7 p)[i.1]! == i.1) = true := by
    apply Finset.filter_congr
    intro i _
    rw [beq_iff_eq]
  rw [hf, e, countFix p 100 le_rfl]
  rfl

theorem any_eq {N : ℕ} {T : ℕ → ℕ} (hT : ∀ i < N, canonK 100 7 (mask 7) (100 * 7) (T i) = true)
    {t : ℕ} (ht : canonK 100 7 (mask 7) (100 * 7) t = true) :
    ((List.range N).map fun i => unpack 100 7 (T i)).any (eqA 100 (unpack 100 7 t)) =
      memK N T t := by
  unfold memK
  rw [CFSG.KC.Misc.ArrEnum.anyNP_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [eqA_F ht (hT i hi)] at h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [eqA_F ht (hT i hi)]⟩

theorem pG_get (G : ℕ → ℕ) (hG : ∀ k < 2, G k = HX.F k) : ∀ k < pGens.size,
    pGens[k]! = unpack 100 7 (G k) := by
  intro k hk
  have hk2 : k < 2 := hk
  rw [pGens_get k hk2, hG k hk2]

theorem zCls : classOK z0 zOrbit 5775 = true := by
  unfold classOK zOrbit classOrbit
  have hN := nums'.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨h1, -, h3⟩ := CFSG.KC.ConjOrb.arrBfs_of_orb (ng := pGens.size) (ngc := ZO.ng)
    (fuel := 20000) (act := classAct) (root := z0) (by rw [nums'.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl)
    (pG_get _ binds'.2.2.2.2.2.2.2.1) (fun _ _ _ => rfl) ZO.h
    (fun i hi => ZO.cl i (by rw [hN] at hi; omega)) (fun i hi => ZO.tr0 i (by rw [hN] at hi; omega))
    (by rw [hN, nums'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num)
    (by rw [binds'.2.2.2.2.2.2.2.2.2.1, z0_eq]) (by rw [z0_eq]; exact validA_unpack (and_of zperm).1)
    keysOK ZO.k (by rw [hN]; norm_num)
  rw [h1, h3, hN]
  rfl

theorem uCls : classOK u0 uOrbit 15400 = true := by
  unfold classOK uOrbit classOrbit
  have hN := nums'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨h1, -, h3⟩ := CFSG.KC.ConjOrb.arrBfs_of_orb (ng := pGens.size) (ngc := UO.ng)
    (fuel := 40000) (act := classAct) (root := u0) (by rw [nums'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl)
    (pG_get _ binds'.2.2.2.2.2.2.2.2.1) (fun _ _ _ => rfl) UO.h
    (fun i hi => UO.cl i (by rw [hN] at hi; omega)) (fun i hi => UO.tr0 i (by rw [hN] at hi; omega))
    (by rw [hN, nums'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]; norm_num)
    (by rw [binds'.2.2.2.2.2.2.2.2.2.2.1, u0_eq]) (by rw [u0_eq]; exact validS (k := 1) (by norm_num))
    keysOK UO.k (by rw [hN]; norm_num)
  rw [h1, h3, hN]
  rfl

theorem yCls : classOK y0 yOrbit 123200 = true := by
  unfold classOK yOrbit classOrbit
  have hN := Clique.nums'.2.1
  obtain ⟨h1, -, h3⟩ := CFSG.KC.ConjOrb.arrBfs_of_orb (ng := pGens.size) (ngc := K3.ng)
    (fuel := 400000) (act := classAct) (root := y0) (by rw [Clique.nums'.1]; decide)
    (pG_get _ (fun k hk => by
      interval_cases k
      · exact Clique.nums'.2.2.1
      · exact Clique.nums'.2.2.2.1)) (fun _ _ _ => rfl) K3.h Clique.hcl
    (fun i hi => K3.tr1 i (by rw [hN] at hi; omega)) (by rw [hN]; decide)
    (by rw [binds'.2.2.2.2.2.2.2.2.2.2.2, y0_eq]) (by rw [y0_eq]; exact validS (k := 0) (by norm_num))
    keysOK K3.k (by rw [hN]; norm_num)
  rw [h1, h3, hN]
  rfl

theorem classesOK_true : classesOK = true := by
  unfold classesOK
  rw [zCls, uCls, yCls, z0_eq, u0_eq, fixCnt_eq, fixCnt_eq, prods'.2.2.2.2.2.2.2.2.2.2.1,
    prods'.2.2.2.2.2.2.2.2.2.2.2]
  rfl

theorem pinOf {ng N fuel : ℕ} {G T E S : ℕ → ℕ} {SK : List ℕ} {gs : Array (Array ℕ)}
    (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack 100 7 (G k))
    (hpp : ∀ k < ng, PP 100 7 (G k)) (hk : bfsK 100 7 ng G N T E S = true)
    (hK : keysSK 100 7 keys N T SK = true) (hf : N ≤ fuel) :
    enumOK 100 gs keys (enumBfs 100 gs keys fuel) = true ∧
      (enumBfs 100 gs keys fuel).pts = Array.ofFn (n := N) fun i => unpack 100 7 (T i.val) :=
  ⟨enumOK_of_bfsK_base hs hg (fun k hk => CFSG.KC.Misc.ArrEnum.permB_of_pp (hpp k hk)) hk keysOK
    hK hf, enumBfs_pts_base hs hg hk keysOK hK hf⟩

theorem kK : keysSK 100 7 keys KK.N KK.T ((List.range 120).map KKK) = true :=
  (and_of (and_of (and_of (and_of keysAll).1).1).1).1
theorem kCY : keysSK 100 7 keys CY.N CY.T ((List.range 360).map CYK) = true :=
  (and_of (and_of (and_of (and_of keysAll).1).1).1).2
theorem kAB : keysSK 100 7 keys AB.N AB.T ((List.range 1440).map ABK) = true :=
  (and_of (and_of (and_of keysAll).1).1).2
theorem kCB : keysSK 100 7 keys CB.N CB.T ((List.range 2880).map CBK) = true :=
  (and_of (and_of keysAll).1).2
theorem kJJ : keysSK 100 7 keys JJ.N JJ.T ((List.range 360).map JJK) = true := (and_of keysAll).2

theorem kPin : enumOK 100 xGens keys kCert = true ∧
    kCert.pts = Array.ofFn (n := KK.N) fun i => unpack 100 7 (KK.T i.val) :=
  pinOf (by rw [nums'.1]; rfl)
    (fun k hk => by rw [nums'.1] at hk; rw [xGens_get k hk, binds'.1 k hk])
    (fun k hk => by rw [nums'.1] at hk; rw [binds'.1 k hk]; exact ppS (c4 k hk)) KK.ok kK
    (by rw [nums'.2.1]; norm_num)

theorem cyGens_get : ∀ k < 5, cyGens[k]! = unpack 100 7 (SX.F k) := by
  intro k hk
  interval_cases k <;> exact tab_eq _ (by norm_num)

theorem cyPin : enumOK 100 cyGens keys cyCert = true ∧
    cyCert.pts = Array.ofFn (n := CY.N) fun i => unpack 100 7 (CY.T i.val) :=
  pinOf (by rw [nums'.2.2.1]; rfl)
    (fun k hk => by rw [nums'.2.2.1] at hk; rw [cyGens_get k hk, binds'.2.1 k hk])
    (fun k hk => by rw [nums'.2.2.1] at hk; rw [binds'.2.1 k hk]; exact ppS (by omega)) CY.ok kCY
    (by rw [nums'.2.2.2.1]; norm_num)

theorem aPin : enumOK 100 aGens keys aCert = true ∧
    aCert.pts = Array.ofFn (n := AB.N) fun i => unpack 100 7 (AB.T i.val) :=
  pinOf (by rw [nums'.2.2.2.2.1]; rfl)
    (fun k hk => by rw [nums'.2.2.2.2.1] at hk; rw [aGens_get k hk, binds'.2.2.1 k hk])
    (fun k hk => by rw [nums'.2.2.2.2.1] at hk; rw [binds'.2.2.1 k hk]; exact ppS (c6 k hk)) AB.ok
    kAB (by rw [nums'.2.2.2.2.2.1]; norm_num)

theorem cuGens_get : ∀ k < 7, cuGens[k]! = unpack 100 7 (CB.G k) := by
  intro k hk
  rcases k with _ | j
  · rw [binds'.2.2.2.1]
    exact tab_eq 1 (by norm_num)
  · have hj : j < 6 := by omega
    rw [binds'.2.2.2.2.1 j hj]
    interval_cases j <;> exact tab_eq _ (by norm_num)

theorem ppCB : ∀ k < 7, PP 100 7 (CB.G k) := by
  intro k hk
  rcases k with _ | j
  · rw [binds'.2.2.2.1]; exact ppS (by norm_num)
  · rw [binds'.2.2.2.2.1 j (by omega)]; exact ppS (c6 j (by omega))

theorem cuPin : enumOK 100 cuGens keys cuCert = true ∧
    cuCert.pts = Array.ofFn (n := CB.N) fun i => unpack 100 7 (CB.T i.val) :=
  pinOf (by rw [nums'.2.2.2.2.2.2.1]; rfl)
    (fun k hk => by rw [nums'.2.2.2.2.2.2.1] at hk; exact cuGens_get k hk)
    (fun k hk => by rw [nums'.2.2.2.2.2.2.1] at hk; exact ppCB k hk) CB.ok kCB
    (by rw [nums'.2.2.2.2.2.2.2.1]; norm_num)

theorem ppJ : ∀ k < 4, PP 100 7 (JJ.G k) := by
  intro k hk
  rw [binds'.2.2.2.2.2.1 k hk]
  exact (ppS (by simp only [Nat.add_eq]; omega)).mul (ppS (by simp only [Nat.add_eq]; omega))

theorem jGens_get : ∀ k < 4, jGens[k]! = unpack 100 7 (JJ.G k) := by
  intro k hk
  rw [binds'.2.2.2.2.2.1 k hk, jGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rw [tab_eq _ (by omega), tab_eq _ (by omega),
    compA_unpack (cS (k := 5 + k) (by omega)) (cS (k := 6 + k) (by omega))]
  rfl

theorem jPin : enumOK 100 jGens keys jCert = true ∧
    jCert.pts = Array.ofFn (n := JJ.N) fun i => unpack 100 7 (JJ.T i.val) :=
  pinOf (by rw [nums'.2.2.2.2.2.2.2.2.1]; rfl)
    (fun k hk => by rw [nums'.2.2.2.2.2.2.2.2.1] at hk; exact jGens_get k hk)
    (fun k hk => by rw [nums'.2.2.2.2.2.2.2.2.1] at hk; exact ppJ k hk) JJ.ok kJJ
    (by rw [nums'.2.2.2.2.2.2.2.2.2.1]; norm_num)

theorem e0Cert_eq : zasE0Cert = enumBfs 100 zasE0Gens (List.range 100) 1000 := rfl

theorem e0Pin : enumOK 100 zasE0Gens zasEKeys zasE0Cert = true ∧
    zasE0Cert.pts = Array.ofFn (n := E0.N) fun i => unpack 100 7 (E0.T i.val) := by
  have hs : zasE0Gens.size = E0.ng := by rw [nums'.2.2.2.2.2.2.2.2.2.2.1]; rfl
  have hg : ∀ k < E0.ng, zasE0Gens[k]! = unpack 100 7 (E0.G k) := fun k hk => by
    rw [nums'.2.2.2.2.2.2.2.2.2.2.1] at hk
    rw [e0_get k hk, binds'.2.2.2.2.2.2.1 k hk]
  have hp : ∀ k < E0.ng, permOK 100 7 (mask 7) (100 * 7) (E0.G k)
      (pinvS 100 7 (mask 7) (E0.G k)) = true := fun k hk => by
    rw [nums'.2.2.2.2.2.2.2.2.2.2.1] at hk
    rw [binds'.2.2.2.2.2.2.1 k hk]
    exact allN_spec (and_of zperm).2 k hk
  have hf : E0.N ≤ 1000 := by rw [nums'.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num
  rw [e0Cert_eq]
  unfold zasEKeys
  exact ⟨enumOK_of_bfsK hs hg hp E0.ok hf, enumBfs_pts hs hg E0.ok hf⟩

theorem mems' : (∀ k < 4, memK E0.N E0.T
      (CFSG.KC.ConjOrb.pconj 100 7 (mask 7) Y0 (pinvS 100 7 (mask 7) Y0) (EX.F k)) = true) ∧
    memK E0.N E0.T Z0 = true ∧ cntK E0.N (fun i => cK Y0 (E0.T i)) = 4 ∧
    memK KK.N KK.T Y0 = false ∧ memK AB.N AB.T U0 = false ∧ memK JJ.N JJ.T Y0 = true ∧
    (∀ g < 6, ∀ k < 4, memK JJ.N JJ.T (CFSG.KC.ConjOrb.pconj 100 7 (mask 7) (SX.F (Nat.add 5 g))
      (pinvS 100 7 (mask 7) (SX.F (Nat.add 5 g))) (JJ.G k)) = true) := by
  have h := mems
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨fun k hk => allN_spec h1 k hk, h2, h3, h4, h5, h6,
    fun g hg k hk => allN_spec (allN_spec h7 g hg) k hk⟩

theorem allLt_false {n : ℕ} {p : ℕ → Bool} {k : ℕ} (hk : k < n) (h : p k = false) :
    allLt n p = false := by
  cases e : allLt n p
  · rfl
  · rw [(allLt_iff.1 e) k hk] at h
    cases h

theorem cE0 : ∀ i < E0.N, canonK 100 7 (mask 7) (100 * 7) (E0.T i) = true := bfsK_canon E0.ok
theorem cKK : ∀ i < KK.N, canonK 100 7 (mask 7) (100 * 7) (KK.T i) = true := bfsK_canon KK.ok
theorem cCY : ∀ i < CY.N, canonK 100 7 (mask 7) (100 * 7) (CY.T i) = true := bfsK_canon CY.ok
theorem cAB : ∀ i < AB.N, canonK 100 7 (mask 7) (100 * 7) (AB.T i) = true := bfsK_canon AB.ok
theorem cJJ : ∀ i < JJ.N, canonK 100 7 (mask 7) (100 * 7) (JJ.T i) = true := bfsK_canon JJ.ok

theorem listOf {c : ArrCert} {N : ℕ} {T : ℕ → ℕ}
    (h : c.pts = Array.ofFn (n := N) fun i => unpack 100 7 (T i.val)) :
    c.pts.toList = (List.range N).map fun i => unpack 100 7 (T i) := by
  rw [h]
  exact pts_toList (fun i => unpack 100 7 (T i))

theorem getOf {c : ArrCert} {N : ℕ} {T : ℕ → ℕ}
    (h : c.pts = Array.ofFn (n := N) fun i => unpack 100 7 (T i.val)) :
    ∀ i < N, c.pts[i]! = unpack 100 7 (T i) := by
  intro i hi
  rw [h, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem cY : canonK 100 7 (mask 7) (100 * 7) Y0 = true := cS (k := 0) (by norm_num)
theorem cU0 : canonK 100 7 (mask 7) (100 * 7) U0 = true := cS (k := 1) (by norm_num)

theorem yOK_true : yOK = true := by
  unfold yOK
  have y1 : eqA 100 (pw y0 3) (idA 100) = true := by
    rw [y0_eq, pw_unpack cY, hidA, eqA_F (ppow_canon cY 3) pidPP.1]
    exact prods'.2.2.2.1
  have y2 : (!eqA 100 y0 (idA 100)) = true := by
    rw [y0_eq, hidA, eqA_F cY pidPP.1, prods'.2.2.2.2.1]
    rfl
  have y3 : commA 100 y0 z0 = true := by
    rw [y0_eq, z0_eq, cK_eq cY ppZ.1]
    exact prods'.2.2.2.2.2.1
  have hsz : zasE0Cert.pts.size = 16 := by
    rw [e0Pin.2, Array.size_ofFn, nums'.2.2.2.2.2.2.2.2.2.2.2.1]
  have y4 : allLt zasE0Gens.size (fun k => zasE0Cert.pts.toList.any
      (eqA 100 (conjA 100 y0 zasE0Gens[k]!))) = true := by
    rw [allLt_iff]
    intro k hk
    have hk4 : k < 4 := hk
    have hEp := allN_spec (and_of zperm).2 k hk4
    rw [listOf e0Pin.2, y0_eq, e0_get k hk4,
      conj_unpack' (p := Y0) sz (allN_spec sperm 0 (by norm_num)) hEp]
    exact (any_eq cE0 (canonK_pcomp cY (canonK_pcomp (pp_of_permB sz hEp).1 (ppS (k := 0)
        (by norm_num)).inv.1))).trans (mems'.1 k hk4)
  have y5 : zasE0Cert.pts.toList.any (eqA 100 z0) = true := by
    rw [listOf e0Pin.2, z0_eq, any_eq cE0 ppZ.1]
    exact mems'.2.1
  have y6 : (eCommCount == 4) = true := by
    have e := card_filter_fin zasE0Cert.pts.size (fun i => commA 100 y0 zasE0Cert.pts[i]!)
    have hc : (List.range E0.N).countP (fun i => commA 100 y0 zasE0Cert.pts[i]!) =
        cntK E0.N (fun i => cK Y0 (E0.T i)) := by
      rw [cntK_eq]
      apply List.countP_congr
      intro i hi
      have hi' := List.mem_range.1 hi
      rw [getOf e0Pin.2 i hi', y0_eq, cK_eq cY (cE0 i hi')]
    unfold eCommCount
    rw [e, hsz, ← nums'.2.2.2.2.2.2.2.2.2.2.2.1, hc, mems'.2.2.1]
    rfl
  rw [y1, y2, y3, e0Pin.1, hsz, y4, y5, y6]
  rfl

theorem coxOK_of {s : Array (Array ℕ)} {S : ℕ → ℕ} {m : ℕ}
    (hs : ∀ i < m, s[i]! = unpack 100 7 (S i))
    (hc : ∀ i < m, canonK 100 7 (mask 7) (100 * 7) (S i) = true) (h : coxK S m = true) :
    coxOK s m = true := by
  unfold coxK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold coxOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro i hi
    rw [hs i hi, compA_unpack (hc i hi) (hc i hi), hidA,
      eqA_F (canonK_pcomp (hc i hi) (hc i hi)) pidPP.1]
    exact allN_spec h1 i hi
  · rw [allLt_iff]
    intro i hi
    have hi0 : i < m := by omega
    have hi1 : i + 1 < m := by omega
    rw [hs i hi0, hs (i + 1) hi1, compA_unpack (hc i hi0) (hc _ hi1),
      compA_unpack (canonK_pcomp (hc i hi0) (hc _ hi1)) (hc i hi0),
      compA_unpack (hc _ hi1) (hc i hi0), compA_unpack (canonK_pcomp (hc _ hi1) (hc i hi0)) (hc _ hi1),
      eqA_F (canonK_pcomp (canonK_pcomp (hc i hi0) (hc _ hi1)) (hc i hi0))
        (canonK_pcomp (canonK_pcomp (hc _ hi1) (hc i hi0)) (hc _ hi1))]
    exact allN_spec h2 i hi
  · rw [allLt_iff]
    intro i hi
    rw [allLt_iff]
    intro j hj
    have h' := allN_spec (allN_spec h3 i hi) j hj
    have e : eqA 100 (compA 100 (unpack 100 7 (S i)) (unpack 100 7 (S j)))
        (compA 100 (unpack 100 7 (S j)) (unpack 100 7 (S i))) = cK (S i) (S j) :=
      cK_eq (hc i hi) (hc j hj)
    rw [hs i hi, hs j hj, e]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Nat.blt_eq] at h' ⊢
    exact h'

theorem coxX : coxOK xGens 4 = true :=
  coxOK_of xGens_get (fun i hi => cS (c4 i hi)) coxXK

theorem coxR : coxOK rGens 5 = true :=
  coxOK_of rGens_get (fun i hi => cS (c6 i (by omega))) coxRK

theorem notId {p q : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true)
    (hq : canonK 100 7 (mask 7) (100 * 7) q = true)
    (h : Nat.beq (pcomp 100 7 (mask 7) p q) (pidn 100 7) = false) :
    (!eqA 100 (compA 100 (unpack 100 7 p) (unpack 100 7 q)) (idA 100)) = true := by
  rw [compA_unpack hp hq, hidA, eqA_F (canonK_pcomp hp hq) pidPP.1, h]
  rfl

theorem kOK_true : kOK = true := by
  unfold kOK
  have k2 : (!eqA 100 (compA 100 xGens[0]! xGens[1]!) (idA 100)) = true := by
    rw [xGens_get 0 (by norm_num), xGens_get 1 (by norm_num)]
    exact notId (cS (by norm_num)) (cS (by norm_num)) prods'.2.2.2.2.2.2.1
  have hsz1 : kCert.pts.size = 120 := by rw [kPin.2, Array.size_ofFn, nums'.2.1]
  have hsz2 : cyCert.pts.size = 360 := by rw [cyPin.2, Array.size_ofFn, nums'.2.2.2.1]
  have k5 : allLt xGens.size (fun k => commA 100 y0 xGens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk4 : k < 4 := hk
    rw [xGens_get k hk4, y0_eq, cK_eq cY (cS (c4 k hk4))]
    exact prods'.2.2.2.2.2.2.2.2.1 k hk4
  have k8 : (!kCert.pts.toList.any (eqA 100 y0)) = true := by
    rw [listOf kPin.2, y0_eq, any_eq cKK cY, mems'.2.2.2.1]
    rfl
  rw [coxX, k2, kPin.1, hsz1, k5, cyPin.1, hsz2, k8]
  rfl

theorem cyAll' : ∀ i < CY.N, (!(allN 4 fun k => cK (CY.T i) (JJ.G k)) ||
    Nat.beq (CY.T i) (pidn 100 7) || Nat.beq (CY.T i) U0) = true := fun i hi => allN_spec cyAll i hi

theorem aOK_true : aOK = true := by
  unfold aOK
  have a2 : (!eqA 100 (compA 100 rGens[0]! rGens[1]!) (idA 100)) = true := by
    rw [rGens_get 0 (by norm_num), rGens_get 1 (by norm_num)]
    exact notId (cS (by norm_num)) (cS (by norm_num)) prods'.2.2.2.2.2.2.2.1
  have a3 : allLt aGens.size (fun k => commA 100 u0 aGens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk6 : k < 6 := hk
    rw [aGens_get k hk6, u0_eq, cK_eq cU0 (cS (c6 k hk6))]
    exact prods'.2.2.2.2.2.2.2.2.2.1 k hk6
  have s1 : aCert.pts.size = 1440 := by rw [aPin.2, Array.size_ofFn, nums'.2.2.2.2.2.1]
  have s2 : cuCert.pts.size = 2880 := by rw [cuPin.2, Array.size_ofFn, nums'.2.2.2.2.2.2.2.1]
  have s3 : jCert.pts.size = 360 := by rw [jPin.2, Array.size_ofFn, nums'.2.2.2.2.2.2.2.2.2.1]
  have a6 : (!aCert.pts.toList.any (eqA 100 u0)) = true := by
    rw [listOf aPin.2, u0_eq, any_eq cAB cU0, mems'.2.2.2.2.1]
    rfl
  have a9 : jCert.pts.toList.any (eqA 100 y0) = true := by
    rw [listOf jPin.2, y0_eq, any_eq cJJ cY]
    exact mems'.2.2.2.2.2.1
  have a10 : allLt aGens.size (fun g => allLt jGens.size (fun k =>
      jCert.pts.toList.any (eqA 100 (conjA 100 aGens[g]! jGens[k]!)))) = true := by
    rw [allLt_iff]
    intro g hg
    have hg6 : g < 6 := hg
    rw [allLt_iff]
    intro k hk
    have hk4 : k < 4 := hk
    have hp := allN_spec sperm _ (c6 g hg6)
    rw [aGens_get g hg6, jGens_get k hk4, listOf jPin.2,
      conj_unpack' sz hp (CFSG.KC.Misc.ArrEnum.permB_of_pp (ppJ k hk4))]
    exact (any_eq cJJ (canonK_pcomp (cS (c6 g hg6)) (canonK_pcomp (ppJ k hk4).1
      (ppS (c6 g hg6)).inv.1))).trans (mems'.2.2.2.2.2.2 g hg6 k hk4)
  have a11 : (cyCert.pts.toList.all fun c => !(allLt jGens.size (fun k => commA 100 c jGens[k]!)) ||
      eqA 100 c (idA 100) || eqA 100 c u0) = true := by
    rw [listOf cyPin.2, List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' := List.mem_range.1 hi
    have hc := cCY i hi'
    have h := cyAll' i hi'
    rw [hidA, eqA_F hc pidPP.1, u0_eq, eqA_F hc cU0]
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
    rcases h with (h | h) | h
    · refine Or.inl (Or.inl ?_)
      cases e : allN 4 (fun k => cK (CY.T i) (JJ.G k))
      · have : ¬ ∀ k < 4, cK (CY.T i) (JJ.G k) = true := fun hall => by
          rw [CFSG.KC.BfsPin.allN_intro hall] at e; cases e
        push Not at this
        obtain ⟨k, hk, hf⟩ := this
        refine allLt_false (k := k) hk ?_
        rw [jGens_get k hk, cK_eq hc (ppJ k hk).1]
        simpa using hf
      · rw [e] at h; cases h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  rw [coxR, a2, a3, aPin.1, s1, a6, cuPin.1, s2, jPin.1, s3, a9, a10, a11]
  rfl

theorem ord3_any {x : ℕ} (hx : canonK 100 7 (mask 7) (100 * 7) x = true) :
    ord3J.any (fun b => commA 100 (unpack 100 7 x) b) =
      CFSG.KC.LQT.P.anyN JJ.N (fun j => ord3K (JJ.T j) && cK x (JJ.T j)) := by
  unfold ord3J
  rw [listOf jPin.2, CFSG.KC.Misc.ArrEnum.anyNP_eq, List.any_filter, List.any_map]
  have hpt : ∀ i < JJ.N, (eqA 100 (pw (unpack 100 7 (JJ.T i)) 3) (idA 100) &&
      !eqA 100 (unpack 100 7 (JJ.T i)) (idA 100) &&
      commA 100 (unpack 100 7 x) (unpack 100 7 (JJ.T i))) = (ord3K (JJ.T i) && cK x (JJ.T i)) := by
    intro i hi
    have hc := cJJ i hi
    rw [pw_unpack hc, hidA, eqA_F (ppow_canon hc 3) pidPP.1, eqA_F hc pidPP.1, cK_eq hx hc]
    rfl
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [hpt i hi] at h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [hpt i hi]⟩

theorem beq_nat (a b : ℕ) : (a == b) = Nat.beq a b :=
  Bool.eq_iff_iff.2 (by rw [beq_iff_eq, Nat.beq_eq])

theorem tableOK_true : tableOK = true := by
  unfold tableOK
  rw [listOf aPin.2, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi' := List.mem_range.1 hi
  have hc := cAB i hi'
  have h := allN_spec table i hi'
  unfold tablePt at h
  rw [CFSG.KC.ConjOrb.strictB_eq] at h
  unfold tableOne
  rw [compA_unpack hc hc, hidA, eqA_F (canonK_pcomp hc hc) pidPP.1, eqA_F hc pidPP.1,
    listOf jPin.2, any_eq cJJ hc, ord3_any hc, fixCnt_eq, u0_eq, compA_unpack cU0 hc, fixCnt_eq]
  unfold invoK tableB at h
  simp only [beq_nat]
  rw [Bool.and_comm (!Nat.beq (AB.T i) (pidn 100 7))] at h
  exact h

theorem s0OK_true : s0OK = true := by
  unfold s0OK
  rw [basicOK_true, classesOK_true, yOK_true, kOK_true, aOK_true, tableOK_true]
  rfl

end CertificateChecks.KernelMisc.HS100.S0

end
