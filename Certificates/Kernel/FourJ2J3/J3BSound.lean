module

public import Certificates.Kernel.J3Ref.Faith
public import CFSG.Certificates.Kernel.FourJBfsBSound
public import CFSG.Certificates.Kernel.FourJoinedKSound
public import Certificates.Kernel.FourJ2J3.J3Checks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFourJ.J3B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnumB CFSG.KC.FourJ CFSG.KC.FourJB
open CertificateChecks.KernelSporSch CertificateChecks.KernelJ3Ref
open CFSG.KC.Misc.ArrEnum CFSG.RankThree.Native CFSG.KC.Q16BK CFSG.KC.BfsPin CFSG.KC.PGrp

theorem j3bFaith : BaseFaith 6156 13 [0, 1, 3, 2, 5766] MJ :=
  baseFaith_ext mj_faith (by decide) (by decide)

theorem letters_M
    (hc : (canonK 6156 13 (mask 13) (6156 * 13) (PJ3.S 0) &&
      canonK 6156 13 (mask 13) (6156 * 13) (PJ3.S 1) &&
      canonK 6156 13 (mask 13) (6156 * 13) (PJ3.SI 0) &&
      canonK 6156 13 (mask 13) (6156 * 13) (PJ3.SI 1)) = true)
    (hw : (wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [1] (PJ3.S 0) &&
      wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [2] (PJ3.S 1) &&
      wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [-1] (PJ3.SI 0) &&
      wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [-2] (PJ3.SI 1)) = true) :
    MJ (PJ3.S 0) ∧ MJ (PJ3.S 1) ∧ MJ (PJ3.SI 0) ∧ MJ (PJ3.SI 1) := by
  simp only [Bool.and_eq_true] at hc hw
  obtain ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩ := hc
  obtain ⟨⟨⟨w0, w1⟩, w2⟩, w3⟩ := hw
  exact ⟨mj_of_word c0 w0, mj_of_word c1 w1, mj_of_word c2 w2, mj_of_word c3 w3⟩

theorem wordT_MJ {O L : Nat → Nat} (hl : ∀ l, MJ (let4 (PJ3.S 0) (PJ3.S 1) (PJ3.SI 0) (PJ3.SI 1) l))
    (t : Nat) : MJ (wordT 6156 13 (let4 (PJ3.S 0) (PJ3.S 1) (PJ3.SI 0) (PJ3.SI 1)) O L t) :=
  wordR_M j3bFaith hl _ _

theorem permB_of_MJ {X : Nat} (h : MJ X) : permB 6156 13 X = true := by
  obtain ⟨hc, A, -, hA⟩ := h
  refine CFSG.KC.Misc.ArrEnum.permB_of_pp ⟨hc, fun i hi => (PF.canon_facts hc).2.2.2 i hi,
    fun a ha b hb e => ?_⟩
  rw [hA ⟨a, ha⟩, hA ⟨b, hb⟩] at e
  exact congrArg Fin.val (A.injective (Fin.ext e))

open CFSG.Monster.B.Co2 (permOfArr) in
theorem pg_eq_perm {X : Nat} (h : MJ X) (x : Fin 6156) :
    pg 13 (mask 13) X x = (permOfArr 6156 (unpack 6156 13 X) x : Nat) := by
  rw [← rep_of_validA (validA_unpack (permB_of_MJ h)) x, CFSG.KC.BfsPin.unpack_getElem!, if_pos x.2]

open CFSG.Monster.B.Co2 (permOfArr) in
theorem eq_of_perm {X Y : Nat} (hX : MJ X) (hY : MJ Y)
    (h : permOfArr 6156 (unpack 6156 13 X) = permOfArr 6156 (unpack 6156 13 Y)) : X = Y :=
  j3bFaith.eq X Y hX hY fun b hb => by
    have hb' := j3bFaith.bs_lt b hb
    rw [pg_eq_perm hX ⟨b, hb'⟩, pg_eq_perm hY ⟨b, hb'⟩, h]

open CFSG.Monster.B.Co2 (permOfArr) in
theorem tree_group {ng N : Nat} {G PAR LAB POS I S : Nat → Nat} {act : Nat → Nat → Nat}
    (hN : 0 < N) (hG : ∀ k < ng, MJ (G k)) (hact : ∀ k < ng, ∀ x < 6156, act k x = pg 13 (mask 13) (G k) x)
    (h : bfsBK [0, 1, 3, 2, 5766] 5 4 ng N act PAR LAB POS I S = true) :
    (∀ i < N, MJ (treeWB 6156 13 G PAR LAB i)) ∧
    (∀ i < N, permOfArr 6156 (unpack 6156 13 (treeWB 6156 13 G PAR LAB i)) ∈
      Subgroup.closure (permsA 6156 (gsK 6156 13 ng G))) ∧
    (∀ z ∈ Subgroup.closure (permsA 6156 (gsK 6156 13 ng G)),
      ∃ i < N, permOfArr 6156 (unpack 6156 13 (treeWB 6156 13 G PAR LAB i)) = z) ∧
    Nat.card (Subgroup.closure (permsA 6156 (gsK 6156 13 ng G))) = N := by
  classical
  obtain ⟨h0, hM, -, hpos, hinj⟩ := bfsBK_sound j3bFaith hG hact h
  obtain ⟨-, -, -, htr, -, -⟩ := bfsBK_spec h
  have hsz : szOK 6156 13 = true := szOK_j3
  set K := Subgroup.closure (permsA 6156 (gsK 6156 13 ng G))
  set T := treeWB 6156 13 G PAR LAB
  have hs : (gsK 6156 13 ng G).size = ng := Array.size_ofFn
  have hg : ∀ k < ng, (gsK 6156 13 ng G)[k]! = unpack 6156 13 (G k) := fun k hkg => by
    unfold gsK
    rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hkg), Array.getElem_ofFn]
  have hGK : ∀ k < ng, permOfArr 6156 (unpack 6156 13 (G k)) ∈ K := fun k hk => by
    rw [← hg k hk]
    exact Subgroup.subset_closure ⟨k, by rw [hs]; exact hk, rfl⟩
  have hmul : ∀ i < N, ∀ k < ng, permOfArr 6156 (unpack 6156 13 (T (POS (i * ng + k)))) =
      permOfArr 6156 (unpack 6156 13 (G k)) * permOfArr 6156 (unpack 6156 13 (T i)) :=
    fun i hi k hk => by
      rw [(hpos i hi k hk).2, permOfArr_pcomp hsz (permB_of_MJ (hG k hk)) (permB_of_MJ (hM i hi))]
  have hmem : ∀ i < N, permOfArr 6156 (unpack 6156 13 (T i)) ∈ K := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [h0, one_pidn hsz]
        exact K.one_mem
      · obtain ⟨hp, hl, -⟩ := htr i hi hi0
        have e : T i = pcomp 6156 13 (mask 13) (G (LAB i)) (T (PAR i)) := treeWB_pos hi0 hp
        rw [e, permOfArr_pcomp hsz (permB_of_MJ (hG _ hl)) (permB_of_MJ (hM _ (by omega)))]
        exact K.mul_mem (hGK _ hl) (ih _ hp (by omega))
  have pinj : ∀ a < N, ∀ b < N,
      permOfArr 6156 (unpack 6156 13 (T a)) = permOfArr 6156 (unpack 6156 13 (T b)) → a = b :=
    fun a ha b hb e => hinj a ha b hb (eq_of_perm (hM a ha) (hM b hb) e)
  have hsurj : ∀ k < ng, ∀ i < N, ∃ j < N, POS (j * ng + k) = i := by
    intro k hk i hi
    let f : Fin N → Fin N := fun j => ⟨POS (j * ng + k), (hpos j j.2 k hk).1⟩
    have hf : Function.Injective f := fun a b e => by
      have e' := congrArg (fun c : Fin N => permOfArr 6156 (unpack 6156 13 (T c))) e
      simp only [f, hmul a a.2 k hk, hmul b b.2 k hk, mul_right_inj] at e'
      exact Fin.ext (pinj _ a.2 _ b.2 e')
    obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.1 hf) ⟨i, hi⟩
    exact ⟨j, j.2, congrArg Fin.val hj⟩
  have hex : ∀ z ∈ K, ∃ i < N, permOfArr 6156 (unpack 6156 13 (T i)) = z := by
    intro z hz
    induction hz using Subgroup.closure_induction_left with
    | one => exact ⟨0, hN, by rw [h0, one_pidn hsz]⟩
    | mul_left x hx y _ ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨k, hk1, rfl⟩ := hx
      have hk : k < ng := by rw [← hs]; exact hk1
      refine ⟨_, (hpos i hi k hk).1, ?_⟩
      change _ = permOfArr 6156 (gsK 6156 13 ng G)[k]! * _
      rw [hg k hk, hmul i hi k hk]
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨k, hk1, rfl⟩ := hx
      have hk : k < ng := by rw [← hs]; exact hk1
      obtain ⟨j, hj, e⟩ := hsurj k hk i hi
      refine ⟨j, hj, ?_⟩
      change _ = (permOfArr 6156 (gsK 6156 13 ng G)[k]!)⁻¹ * _
      rw [hg k hk, ← e, hmul j hj k hk, inv_mul_cancel_left]
  refine ⟨hM, hmem, hex, ?_⟩
  let f : Fin N → K := fun i => ⟨_, hmem i i.2⟩
  have hf : Function.Bijective f := ⟨fun a b e => Fin.ext (pinj _ a.2 _ b.2 (congrArg Subtype.val e)),
    fun ⟨z, hz⟩ => by
      obtain ⟨i, hi, rfl⟩ := hex z hz
      exact ⟨⟨i, hi⟩, rfl⟩⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem lt_of_MJ {X x : Nat} (h : MJ X) (hx : x < 6156) : pg 13 (mask 13) X x < 6156 :=
  (PF.canon_facts h.1).2.2.2 x hx

theorem chaseP_eq {lf L : Nat → Nat} {pm : Nat → Nat → Nat} (hl : ∀ l, MJ (lf l))
    (hpm : ∀ l, ∀ x < 6156, pm l x = pg 13 (mask 13) (lf l) x) :
    ∀ len o, ∀ x < 6156, chaseP pm L len o x = pg 13 (mask 13) (wordR 6156 13 lf L len o) x
  | 0, _, x, hx => (PF.pg_pidn (by norm_num) (by norm_num) hx).symm
  | len + 1, o, x, hx => by
    change pm (L o) (chaseP pm L len (o + 1) x) =
      pg 13 (mask 13) (pcomp 6156 13 (mask 13) (lf (L o)) (wordR 6156 13 lf L len (o + 1))) x
    rw [PF.pg_pcomp (by norm_num) hx, chaseP_eq hl hpm len (o + 1) x hx,
      hpm _ _ (lt_of_MJ (wordR_M j3bFaith hl len (o + 1)) hx)]

theorem treeCh_eq {ng N : Nat} {G PAR LAB : Nat → Nat} {act : Nat → Nat → Nat}
    (hact : ∀ k < ng, ∀ x < 6156, act k x = pg 13 (mask 13) (G k) x)
    (htr : ∀ c < N, c ≠ 0 → PAR c < c ∧ LAB c < ng)
    (hM : ∀ i < N, MJ (treeWB 6156 13 G PAR LAB i)) :
    ∀ fuel a, a ≤ fuel → a < N → ∀ x < 6156,
      treeCh act PAR LAB fuel a x = pg 13 (mask 13) (treeWB 6156 13 G PAR LAB a) x
  | 0, a, ha, _, x, hx => by
    obtain rfl : a = 0 := by omega
    rw [treeWB_zero, PF.pg_pidn (by norm_num) (by norm_num) hx]
    rfl
  | fuel + 1, a, ha, haN, x, hx => by
    by_cases h0 : a = 0
    · subst h0
      rw [treeWB_zero, PF.pg_pidn (by norm_num) (by norm_num) hx]
      rfl
    · obtain ⟨hp, hl⟩ := htr a haN h0
      have hb : Nat.beq a 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      have e : treeCh act PAR LAB (fuel + 1) a x =
          act (LAB a) (treeCh act PAR LAB fuel (PAR a) x) := by
        change nIf(Nat.beq a (nat_lit 0), x, act (LAB a) (treeCh act PAR LAB fuel (PAR a) x)) = _
        rw [hb]
      rw [e, treeCh_eq hact htr hM fuel (PAR a) (by omega) (by omega) x hx, treeWB_pos h0 hp,
        PF.pg_pcomp (by norm_num) hx, hact _ hl _ (lt_of_MJ (hM _ (by omega)) hx)]

theorem pcomp_assocJ {X Y Z : Nat} (hX : MJ X) (hY : MJ Y) (hZ : MJ Z) :
    pcomp 6156 13 (mask 13) (pcomp 6156 13 (mask 13) X Y) Z =
      pcomp 6156 13 (mask 13) X (pcomp 6156 13 (mask 13) Y Z) :=
  j3bFaith.eq _ _ (j3bFaith.comp _ _ (j3bFaith.comp _ _ hX hY) hZ)
    (j3bFaith.comp _ _ hX (j3bFaith.comp _ _ hY hZ)) fun b hb => by
      have hb' := j3bFaith.bs_lt b hb
      rw [PF.pg_pcomp (by norm_num) hb', PF.pg_pcomp (by norm_num) hb',
        PF.pg_pcomp (by norm_num) hb', PF.pg_pcomp (by norm_num) (lt_of_MJ hZ hb')]

theorem pidn_compJ {X : Nat} (hX : MJ X) : pcomp 6156 13 (mask 13) (pidn 6156 13) X = X :=
  j3bFaith.eq _ _ (j3bFaith.comp _ _ j3bFaith.id hX) hX fun b hb => by
    have hb' := j3bFaith.bs_lt b hb
    rw [PF.pg_pcomp (by norm_num) hb', PF.pg_pidn (by norm_num) (by norm_num) (lt_of_MJ hX hb')]

theorem mt_sound {ng N : Nat} {G PAR LAB POS MT : Nat → Nat}
    (hG : ∀ k < ng, MJ (G k)) (htr : ∀ c < N, c ≠ 0 → PAR c < c ∧ LAB c < ng)
    (hM : ∀ i < N, MJ (treeWB 6156 13 G PAR LAB i))
    (hpos : ∀ i < N, ∀ k < ng, POS (i * ng + k) < N ∧ treeWB 6156 13 G PAR LAB (POS (i * ng + k)) =
      pcomp 6156 13 (mask 13) (G k) (treeWB 6156 13 G PAR LAB i))
    (h : mtBK N ng PAR LAB POS MT = true) :
    ∀ a < N, ∀ b < N, mtI N MT a b < N ∧ treeWB 6156 13 G PAR LAB (mtI N MT a b) =
      pcomp 6156 13 (mask 13) (treeWB 6156 13 G PAR LAB a) (treeWB 6156 13 G PAR LAB b) := by
  have hs : ∀ a < N, ∀ b < N, mtI N MT a b < N ∧ (a = 0 → mtI N MT a b = b) ∧
      (a ≠ 0 → mtI N MT a b = POS (mtI N MT (PAR a) b * ng + LAB a)) := by
    intro a ha b hb
    have e := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h a ha) b hb
    by_cases h0 : a = 0
    · subst h0
      simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
        Nat.blt_eq] at e
      exact ⟨e.1, fun _ => Nat.eq_of_beq_eq_true e.2, fun h => absurd rfl h⟩
    · have hb0 : Nat.beq a 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
        Nat.blt_eq, hb0] at e
      exact ⟨e.1, fun h => absurd h h0, fun _ => Nat.eq_of_beq_eq_true e.2⟩
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha b hb
    obtain ⟨h1, h2, h3⟩ := hs a ha b hb
    refine ⟨h1, ?_⟩
    by_cases h0 : a = 0
    · subst h0
      rw [h2 rfl, treeWB_zero, pidn_compJ (hM b hb)]
    · obtain ⟨hp, hl⟩ := htr a ha h0
      obtain ⟨i1, i2⟩ := ih _ hp (by omega) b hb
      rw [h3 h0, (hpos _ i1 _ hl).2, i2, treeWB_pos h0 hp,
        pcomp_assocJ (hG _ hl) (hM _ (by omega)) (hM b hb)]

open CFSG.Monster.B.Co2 (permOfArr) in
theorem conjJ {g x y : Nat} (hg : MJ g) (hx : MJ x) (hy : MJ y)
    (h : pcomp 6156 13 (mask 13) g x = pcomp 6156 13 (mask 13) y g) :
    permOfArr 6156 (unpack 6156 13 g) * permOfArr 6156 (unpack 6156 13 x) *
      (permOfArr 6156 (unpack 6156 13 g))⁻¹ = permOfArr 6156 (unpack 6156 13 y) := by
  have e : permOfArr 6156 (unpack 6156 13 (pcomp 6156 13 (mask 13) g x)) =
      permOfArr 6156 (unpack 6156 13 (pcomp 6156 13 (mask 13) y g)) := by rw [h]
  rw [permOfArr_pcomp szOK_j3 (permB_of_MJ hg) (permB_of_MJ hx),
    permOfArr_pcomp szOK_j3 (permB_of_MJ hy) (permB_of_MJ hg)] at e
  rw [e, mul_inv_cancel_right]

theorem getD_memJ {cs : List Nat} {b : Nat} (hb : b ∈ cs) : ∃ c < cs.length, cs.getD c 0 = b := by
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hb
  exact ⟨c, hc, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]⟩

theorem selI_cases (N : Nat) (MT : Nat → Nat) (x y c : Nat) :
    selI N MT x y c = x ∨ selI N MT x y c = y ∨ selI N MT x y c = mtI N MT x y := by
  unfold selI
  cases Nat.beq c (nat_lit 0)
  · cases Nat.beq c (nat_lit 1)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem pmX_eq {nX : Nat} {Z ZI : Nat → Nat} {pz pzi : Nat → Nat → Nat}
    (hz : ∀ k, ∀ x < 6156, pz k x = pg 13 (mask 13) (Z k) x)
    (hzi : ∀ k, ∀ x < 6156, pzi k x = pg 13 (mask 13) (ZI k) x) (l x : Nat) (hx : x < 6156) :
    pmX nX pz pzi l x = pg 13 (mask 13) (letX 6156 13 nX Z ZI l) x := by
  unfold pmX letX
  cases Nat.blt l nX
  · cases Nat.blt l (Nat.add nX nX)
    · exact (PF.pg_pidn (by norm_num) (by norm_num) hx).symm
    · exact hzi _ x hx
  · exact hz _ x hx

open CFSG.Monster.B.Co2 (permOfArr) in
open CFSG.ComponentClassification.Sol76.Sig.GSYard02 in
theorem j3_fourJoined : ∃ K : Subgroup (Equiv.Perm (Fin 6156)),
    K ≤ subP 6156 13 (PJ3.S 0) (PJ3.S 1) ∧ Nat.card K = 128 ∧
      Nonempty (FourJoinedData (subP 6156 13 (PJ3.S 0) (PJ3.S 1)) K) := by
  classical
  have hsz : szOK 6156 13 = true := szOK_j3
  have hN : J3D.N = 128 := by
    have h := J3.nums
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1
  have hsN : 0 < J3D.N := by rw [hN]; norm_num
  obtain ⟨mA, mB, mAI, mBI⟩ := letters_M J3.letC J3.letW
  have hl : ∀ l, MJ (J3.l4J l) := let4_mem (P := MJ) mA mB mAI mBI
  have hwM : ∀ (O L : Nat → Nat) t, MJ (wordT 6156 13 J3.l4J O L t) :=
    fun _ _ _ => wordR_M j3bFaith hl _ _
  have hwE : ∀ (O L : Nat → Nat) t, ∀ x < 6156,
      chaseT 13 J3.l4J O L t x = pg 13 (mask 13) (wordT 6156 13 J3.l4J O L t) x :=
    fun _ _ t x hx => chaseT_eq j3bFaith t x hx
  have hG : ∀ k < J3D.ng, MJ (wordT 6156 13 J3.l4J J3D.SO J3D.SL k) := fun k _ => hwM _ _ k
  have hact : ∀ k < J3D.ng, ∀ x < 6156,
      J3.actJ k x = pg 13 (mask 13) (wordT 6156 13 J3.l4J J3D.SO J3D.SL k) x :=
    fun k _ x hx => hwE _ _ k x hx
  have hbfs := J3.bfsB
  obtain ⟨hM, hmem, hex, hcard⟩ := tree_group hsN hG hact hbfs
  obtain ⟨h0, -, himg, hpos, hinj⟩ := bfsBK_sound j3bFaith hG hact hbfs
  obtain ⟨-, -, -, htr0, -, -⟩ := bfsBK_spec hbfs
  have htr : ∀ c < J3D.N, c ≠ 0 → J3D.BPAR c < c ∧ J3D.BLAB c < J3D.ng :=
    fun c hc hc0 => ⟨(htr0 c hc hc0).1, (htr0 c hc hc0).2.1⟩
  set G := wordT 6156 13 J3.l4J J3D.SO J3D.SL with hGd
  set T := treeWB 6156 13 G J3D.BPAR J3D.BLAB with hTd
  set K := Subgroup.closure (permsA 6156 (gsK 6156 13 J3D.ng G)) with hKd
  set P := subP 6156 13 (PJ3.S 0) (PJ3.S 1) with hPd
  have hT0' : permOfArr 6156 (unpack 6156 13 (T 0)) = 1 := by
    rw [h0]
    exact one_pidn hsz
  have pinj : ∀ a < J3D.N, ∀ b < J3D.N, permOfArr 6156 (unpack 6156 13 (T a)) =
      permOfArr 6156 (unpack 6156 13 (T b)) → a = b :=
    fun a ha b hb e => hinj a ha b hb (eq_of_perm (hM a ha) (hM b hb) e)
  have hmt : ∀ a < J3D.N, ∀ b < J3D.N, mtI J3D.N J3D.BMT a b < J3D.N ∧
      T (mtI J3D.N J3D.BMT a b) = pcomp 6156 13 (mask 13) (T a) (T b) :=
    mt_sound hG htr hM hpos J3.mt
  have hmul : ∀ a < J3D.N, ∀ b < J3D.N, permOfArr 6156 (unpack 6156 13 (T a)) *
      permOfArr 6156 (unpack 6156 13 (T b)) =
        permOfArr 6156 (unpack 6156 13 (T (mtI J3D.N J3D.BMT a b))) := fun a ha b hb => by
    rw [(hmt a ha b hb).2, permOfArr_pcomp hsz (permB_of_MJ (hM a ha)) (permB_of_MJ (hM b hb))]
  have k1 : ∀ {a b c : Nat}, a < J3D.N → b < J3D.N → c < J3D.N →
      (Nat.beq (mtI J3D.N J3D.BMT a b) c = true ↔ permOfArr 6156 (unpack 6156 13 (T a)) *
        permOfArr 6156 (unpack 6156 13 (T b)) = permOfArr 6156 (unpack 6156 13 (T c))) := by
    intro a b c ha hb hc
    rw [Nat.beq_eq, hmul a ha b hb]
    exact ⟨fun e => by rw [e], fun e => pinj _ (hmt a ha b hb).1 _ hc e⟩
  have k0 : ∀ {a : Nat}, a < J3D.N → (Nat.beq (mtI J3D.N J3D.BMT a a) 0 = true ↔
      permOfArr 6156 (unpack 6156 13 (T a)) * permOfArr 6156 (unpack 6156 13 (T a)) = 1) := by
    intro a ha
    rw [← hT0']
    exact k1 ha ha hsN
  have cm : ∀ {a b : Nat}, a < J3D.N → b < J3D.N → (cmBK J3D.N J3D.BMT a b = true ↔
      permOfArr 6156 (unpack 6156 13 (T a)) * permOfArr 6156 (unpack 6156 13 (T b)) =
        permOfArr 6156 (unpack 6156 13 (T b)) * permOfArr 6156 (unpack 6156 13 (T a))) := by
    intro a b ha hb
    unfold cmBK
    rw [Nat.beq_eq, hmul a ha b hb, hmul b hb a ha]
    exact ⟨fun e => by rw [e], fun e => pinj _ (hmt a ha b hb).1 _ (hmt b hb a ha).1 e⟩
  have hkl := J3.klein
  unfold kleinMK at hkl
  have hKl : ∀ i < J3D.m, J3D.PX i < J3D.N ∧ J3D.PY i < J3D.N ∧ J3D.PXY i < J3D.N ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) ≠ 1 ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) ≠ 1 ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) ≠ permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) = 1 ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) = 1 ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) =
        permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) =
        permOfArr 6156 (unpack 6156 13 (T (J3D.PXY i))) := by
    intro i hi
    have h := CFSG.KS.Raw.Orb.allN_iff.1 hkl i hi
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    have hx := Nat.blt_eq.mp h1
    have hy := Nat.blt_eq.mp h2
    have hxy := Nat.blt_eq.mp h3
    have hx0 : 0 < J3D.PX i := Nat.blt_eq.mp h4
    have hy0 : 0 < J3D.PY i := Nat.blt_eq.mp h5
    have hne : J3D.PX i ≠ J3D.PY i := by
      intro he
      rw [he, Nat.beq_refl] at h6
      exact Bool.noConfusion h6
    refine ⟨hx, hy, hxy, fun e => ?_, fun e => ?_, fun e => hne (pinj _ hx _ hy e),
      (k0 hx).1 h7, (k0 hy).1 h8, (cm hx hy).1 h9, (k1 hx hy hxy).1 h10⟩
    · rw [← hT0'] at e
      have := pinj _ hx _ hsN e
      omega
    · rw [← hT0'] at e
      have := pinj _ hy _ hsN e
      omega
  have htrK := J3.tree
  unfold treeMK at htrK
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at htrK
  obtain ⟨tr1, tr2, tr3⟩ := htrK
  have hnb : 0 < J3D.nBig := Nat.blt_eq.mp tr1
  have hnm : J3D.nBig ≤ J3D.m := Nat.ble_eq.mp tr2
  have hTree : ∀ i, 0 < i → i < J3D.nBig → J3D.PAR i < i ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.PAR i)))) =
        permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.PAR i)))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.PAR i)))) =
        permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.PAR i)))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.PAR i)))) =
        permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.PAR i)))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) ∧
      permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.PAR i)))) =
        permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.PAR i)))) * permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) := by
    intro i hi0 hi
    have h := CFSG.KS.Raw.Orb.allN_iff.1 tr3 i hi
    have hb : Nat.beq i (nat_lit 0) = false := by
      cases e : Nat.beq i (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) (Nat.pos_iff_ne_zero.mp hi0)
    rw [hb] at h
    simp only [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq,
      Bool.and_eq_true, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hpi : J3D.PAR i < i := Nat.blt_eq.mp h1
    obtain ⟨xi, yi, -⟩ := hKl i (by omega)
    obtain ⟨xp, yp, -⟩ := hKl (J3D.PAR i) (by omega)
    exact ⟨hpi, (cm xi xp).1 h2, (cm xi yp).1 h3, (cm yi xp).1 h4, (cm yi yp).1 h5⟩
  have hct : ∀ a < J3D.N, ∀ x < 6156, J3.ctJ a x = pg 13 (mask 13) (T a) x :=
    fun a ha x hx => treeCh_eq hact htr hM J3D.N a (le_of_lt ha) ha x hx
  have hcs : ∀ c < 5, ([0, 1, 3, 2, 5766] : List Nat).getD c 0 < 6156 := fun c hc => by
    interval_cases c <;> decide
  have hI : ∀ a < J3D.N, ∀ c < 5, J3D.BIM (a * 5 + c) < 6156 := fun a ha c hc => by
    rw [← himg a ha c hc]
    exact lt_of_MJ (hM a ha) (hcs c hc)
  have hAP : permOfArr 6156 (unpack 6156 13 (PJ3.S 0)) ∈ P := by
    rw [hPd]
    unfold subP
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hBP : permOfArr 6156 (unpack 6156 13 (PJ3.S 1)) ∈ P := by
    rw [hPd]
    unfold subP
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hinvL := J3.letInv
  unfold invBK at hinvL
  have invE : ∀ {X Y : Nat}, MJ X → MJ Y →
      (∀ c < 5, pg 13 (mask 13) X (pg 13 (mask 13) Y (([0, 1, 3, 2, 5766] : List Nat).getD c 0)) =
        ([0, 1, 3, 2, 5766] : List Nat).getD c 0) →
      permOfArr 6156 (unpack 6156 13 Y) = (permOfArr 6156 (unpack 6156 13 X))⁻¹ := by
    intro X Y hX hY h
    have e : pcomp 6156 13 (mask 13) X Y = pidn 6156 13 :=
      j3bFaith.eq _ _ (j3bFaith.comp _ _ hX hY) j3bFaith.id fun b hb => by
        obtain ⟨c, hc, rfl⟩ := getD_memJ hb
        rw [PF.pg_pcomp (by norm_num) (hcs c hc), h c hc,
          PF.pg_pidn (by norm_num) (by norm_num) (hcs c hc)]
    have e2 := congrArg (fun c => permOfArr 6156 (unpack 6156 13 c)) e
    simp only [permOfArr_pcomp hsz (permB_of_MJ hX) (permB_of_MJ hY), one_pidn hsz] at e2
    exact eq_inv_of_mul_eq_one_right e2
  have hiA : permOfArr 6156 (unpack 6156 13 (PJ3.SI 0)) = (permOfArr 6156 (unpack 6156 13 (PJ3.S 0)))⁻¹ :=
    invE mA mAI fun c hc => by
      have h := CFSG.KS.Raw.Orb.allN_iff.1 hinvL c hc
      simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
      exact Nat.eq_of_beq_eq_true h.1
  have hiB : permOfArr 6156 (unpack 6156 13 (PJ3.SI 1)) = (permOfArr 6156 (unpack 6156 13 (PJ3.S 1)))⁻¹ :=
    invE mB mBI fun c hc => by
      have h := CFSG.KS.Raw.Orb.allN_iff.1 hinvL c hc
      simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
      exact Nat.eq_of_beq_eq_true h.2
  have h4 : ∀ l, permB 6156 13 (J3.l4J l) = true ∧ permOfArr 6156 (unpack 6156 13 (J3.l4J l)) ∈ P :=
    let4_mem (P := fun c => permB 6156 13 c = true ∧ permOfArr 6156 (unpack 6156 13 c) ∈ P)
      ⟨permB_of_MJ mA, hAP⟩ ⟨permB_of_MJ mB, hBP⟩
      ⟨permB_of_MJ mAI, by rw [hiA]; exact P.inv_mem hAP⟩
      ⟨permB_of_MJ mBI, by rw [hiB]; exact P.inv_mem hBP⟩
  have hKP : K ≤ P := by
    rw [hKd, Subgroup.closure_le]
    rintro _ ⟨k, hk1, rfl⟩
    have hk2 : k < J3D.ng := by
      rw [← (Array.size_ofFn : (gsK 6156 13 J3D.ng G).size = J3D.ng)]
      exact hk1
    change permOfArr 6156 (gsK 6156 13 J3D.ng G)[k]! ∈ P
    unfold gsK
    rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk2), Array.getElem_ofFn]
    exact (wordT_mem hsz h4 k).2
  have conjB : ∀ {g x y : Nat}, MJ g → x < J3D.N → y < J3D.N →
      (∀ c < 5, pg 13 (mask 13) g (J3D.BIM (x * 5 + c)) =
        pg 13 (mask 13) (T y) (pg 13 (mask 13) g (([0, 1, 3, 2, 5766] : List Nat).getD c 0))) →
      permOfArr 6156 (unpack 6156 13 g) * permOfArr 6156 (unpack 6156 13 (T x)) *
        (permOfArr 6156 (unpack 6156 13 g))⁻¹ = permOfArr 6156 (unpack 6156 13 (T y)) := by
    intro g x y hg hx hy h
    refine conjJ hg (hM x hx) (hM y hy) (j3bFaith.eq _ _ (j3bFaith.comp _ _ hg (hM x hx))
      (j3bFaith.comp _ _ (hM y hy) hg) fun b hb => ?_)
    obtain ⟨c, hc, rfl⟩ := getD_memJ hb
    rw [PF.pg_pcomp (by norm_num) (hcs c hc), PF.pg_pcomp (by norm_num) (hcs c hc),
      himg x hx c hc, h c hc]
  have hisoK := J3.iso
  unfold isoBK at hisoK
  have hIso : ∀ i, J3D.nBig ≤ i → i < J3D.m →
      ∃ g ∈ P, ∃ j < J3D.nBig,
        g * permOfArr 6156 (unpack 6156 13 (T (J3D.PX j))) * g⁻¹ = permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) ∧
        g * permOfArr 6156 (unpack 6156 13 (T (J3D.PY j))) * g⁻¹ = permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) := by
    intro i hi1 hi2
    have ht : i - J3D.nBig < Nat.sub J3D.m J3D.nBig := by
      change i - J3D.nBig < J3D.m - J3D.nBig
      omega
    have h := CFSG.KS.Raw.Orb.allN_iff.1 hisoK (i - J3D.nBig) ht
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    have hi' : Nat.add J3D.nBig (i - J3D.nBig) = i := Nat.add_sub_cancel' hi1
    rw [hi'] at h
    obtain ⟨h1, h2⟩ := h
    have hj : J3D.IJ (i - J3D.nBig) < J3D.nBig := Nat.blt_eq.mp h1
    have hg := hwM J3D.IO J3D.IL (i - J3D.nBig)
    obtain ⟨xj, yj, -⟩ := hKl (J3D.IJ (i - J3D.nBig)) (by omega)
    obtain ⟨xi, yi, -⟩ := hKl i hi2
    have hc := fun c (hc : c < 5) => by
      have e := CFSG.KS.Raw.Orb.allN_iff.1 h2 c hc
      simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
        Nat.add_eq, Nat.mul_eq] at e
      exact e
    refine ⟨_, (wordT_mem hsz h4 (O := J3D.IO) (L := J3D.IL) (i - J3D.nBig)).2, _, hj,
      conjB hg xj xi fun c hcc => ?_, conjB hg yj yi fun c hcc => ?_⟩
    · have e := Nat.eq_of_beq_eq_true (hc c hcc).1
      change chaseT 13 J3.l4J J3D.IO J3D.IL _ _ = treeCh J3.actJ J3D.BPAR J3D.BLAB J3D.N _
        (chaseT 13 J3.l4J J3D.IO J3D.IL _ _) at e
      rw [hwE _ _ _ _ (hI _ xj c hcc), hwE _ _ _ _ (hcs c hcc)] at e
      rw [e]
      exact hct _ xi _ (lt_of_MJ hg (hcs c hcc))
    · have e := Nat.eq_of_beq_eq_true (hc c hcc).2
      change chaseT 13 J3.l4J J3D.IO J3D.IL _ _ = treeCh J3.actJ J3D.BPAR J3D.BLAB J3D.N _
        (chaseT 13 J3.l4J J3D.IO J3D.IL _ _) at e
      rw [hwE _ _ _ _ (hI _ yj c hcc), hwE _ _ _ _ (hcs c hcc)] at e
      rw [e]
      exact hct _ yi _ (lt_of_MJ hg (hcs c hcc))
  have hnormK := J3.norm
  unfold normBK at hnormK
  have hczE : ∀ k, ∀ x < 6156,
      J3.czJ k x = pg 13 (mask 13) (wordT 6156 13 J3.l4J J3D.NO J3D.NL k) x :=
    fun k x hx => hwE _ _ k x hx
  have hcziE : ∀ k, ∀ x < 6156,
      J3.cziJ k x = pg 13 (mask 13) (wordT 6156 13 J3.l4J J3D.NO J3D.BZIL k) x :=
    fun k x hx => hwE _ _ k x hx
  have hNorm : ∀ k < J3D.nX, J3D.NJ k < J3D.nBig ∧
      permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.BZIL k)) =
        (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)))⁻¹ ∧
      (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)) *
          permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) *
          (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)))⁻¹ =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) ∨
        permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)) *
          permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) *
          (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)))⁻¹ =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k)))) ∨
        permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)) *
          permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) *
          (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)))⁻¹ =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) *
              permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k))))) ∧
      (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)) *
          permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k)))) *
          (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)))⁻¹ =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) ∨
        permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)) *
          permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k)))) *
          (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)))⁻¹ =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k)))) ∨
        permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)) *
          permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k)))) *
          (permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)))⁻¹ =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) *
              permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k))))) := by
    intro k hk
    have h := CFSG.KS.Raw.Orb.allN_iff.1 hnormK k hk
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hj : J3D.NJ k < J3D.nBig := Nat.blt_eq.mp h1
    obtain ⟨xj, yj, -⟩ := hKl (J3D.NJ k) (by omega)
    have hc := fun c (hc : c < 5) => by
      have e := CFSG.KS.Raw.Orb.allN_iff.1 h2 c hc
      simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
        Nat.add_eq, Nat.mul_eq] at e
      exact e
    have hz := hwM J3D.NO J3D.NL k
    have hzi := hwM J3D.NO J3D.BZIL k
    have sel : ∀ c, selI J3D.N J3D.BMT (J3D.PX (J3D.NJ k)) (J3D.PY (J3D.NJ k)) c < J3D.N ∧
        (permOfArr 6156 (unpack 6156 13 (T (selI J3D.N J3D.BMT (J3D.PX (J3D.NJ k)) (J3D.PY (J3D.NJ k)) c))) =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) ∨
          permOfArr 6156 (unpack 6156 13 (T (selI J3D.N J3D.BMT (J3D.PX (J3D.NJ k)) (J3D.PY (J3D.NJ k)) c))) =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k)))) ∨
          permOfArr 6156 (unpack 6156 13 (T (selI J3D.N J3D.BMT (J3D.PX (J3D.NJ k)) (J3D.PY (J3D.NJ k)) c))) =
            permOfArr 6156 (unpack 6156 13 (T (J3D.PX (J3D.NJ k)))) *
              permOfArr 6156 (unpack 6156 13 (T (J3D.PY (J3D.NJ k))))) := by
      intro c
      rcases selI_cases J3D.N J3D.BMT (J3D.PX (J3D.NJ k)) (J3D.PY (J3D.NJ k)) c with e | e | e <;>
        rw [e]
      · exact ⟨xj, Or.inl rfl⟩
      · exact ⟨yj, Or.inr (Or.inl rfl)⟩
      · exact ⟨(hmt _ xj _ yj).1, Or.inr (Or.inr (hmul _ xj _ yj).symm)⟩
    obtain ⟨s1, s2⟩ := sel (J3D.NCX k)
    obtain ⟨t1, t2⟩ := sel (J3D.NCY k)
    refine ⟨hj, invE hz hzi fun c hcc => ?_, ?_, ?_⟩
    · have e := Nat.eq_of_beq_eq_true (hc c hcc).1
      rw [hcziE _ _ (hcs c hcc), hczE _ _ (lt_of_MJ hzi (hcs c hcc))] at e
      exact e
    · rw [conjB hz xj s1 fun c hcc => ?_]
      · exact s2
      · have e := Nat.eq_of_beq_eq_true (hc c hcc).2.1
        rw [hczE _ _ (hI _ xj c hcc), hczE _ _ (hcs c hcc),
          hct _ s1 _ (lt_of_MJ hz (hcs c hcc))] at e
        exact e
    · rw [conjB hz yj t1 fun c hcc => ?_]
      · exact t2
      · have e := Nat.eq_of_beq_eq_true (hc c hcc).2.2
        rw [hczE _ _ (hI _ yj c hcc), hczE _ _ (hcs c hcc),
          hct _ t1 _ (lt_of_MJ hz (hcs c hcc))] at e
        exact e
  let X : Set (Equiv.Perm (Fin 6156)) := {z | ∃ k < J3D.nX,
    permOfArr 6156 (unpack 6156 13 (wordT 6156 13 J3.l4J J3D.NO J3D.NL k)) = z}
  have hXl : ∀ l, MJ (letX 6156 13 J3D.nX (wordT 6156 13 J3.l4J J3D.NO J3D.NL)
      (wordT 6156 13 J3.l4J J3D.NO J3D.BZIL) l) :=
    letX_mem (P := MJ) (fun k _ => hwM _ _ k) (fun k _ => hwM _ _ k) j3bFaith.id
  have hX : ∀ l, permB 6156 13 (letX 6156 13 J3D.nX (wordT 6156 13 J3.l4J J3D.NO J3D.NL)
      (wordT 6156 13 J3.l4J J3D.NO J3D.BZIL) l) = true ∧
      permOfArr 6156 (unpack 6156 13 (letX 6156 13 J3D.nX (wordT 6156 13 J3.l4J J3D.NO J3D.NL)
        (wordT 6156 13 J3.l4J J3D.NO J3D.BZIL) l)) ∈ Subgroup.closure X :=
    letX_mem (P := fun c => permB 6156 13 c = true ∧
        permOfArr 6156 (unpack 6156 13 c) ∈ Subgroup.closure X)
      (fun k hk => ⟨permB_of_MJ (hwM _ _ k), Subgroup.subset_closure ⟨k, hk, rfl⟩⟩)
      (fun k hk => ⟨permB_of_MJ (hwM _ _ k), by
        rw [(hNorm k hk).2.1]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨k, hk, rfl⟩)⟩)
      ⟨permB_of_pp (PP.id hsz), by rw [one_pidn hsz]; exact Subgroup.one_mem _⟩
  have hU : ∀ t, ∀ x < 6156, J3.cuJ t x = pg 13 (mask 13) (wordT 6156 13
      (letX 6156 13 J3D.nX (wordT 6156 13 J3.l4J J3D.NO J3D.NL)
        (wordT 6156 13 J3.l4J J3D.NO J3D.BZIL)) J3D.UO J3D.UL t) x :=
    fun t x hx => chaseP_eq hXl (fun l y hy => pmX_eq hczE hcziE l y hy) _ _ x hx
  have hgenK := J3.gen
  unfold genBK at hgenK
  have hgc := fun c (hc : c < 5) => by
    have e := CFSG.KS.Raw.Orb.allN_iff.1 hgenK c hc
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at e
    exact e
  have hAeq : PJ3.S 0 = wordT 6156 13 (letX 6156 13 J3D.nX (wordT 6156 13 J3.l4J J3D.NO J3D.NL)
      (wordT 6156 13 J3.l4J J3D.NO J3D.BZIL)) J3D.UO J3D.UL 0 :=
    j3bFaith.eq _ _ mA (wordR_M j3bFaith hXl _ _) fun b hb => by
      obtain ⟨c, hc, rfl⟩ := getD_memJ hb
      rw [Nat.eq_of_beq_eq_true (hgc c hc).1, hU 0 _ (hcs c hc)]
  have hBeq : PJ3.S 1 = wordT 6156 13 (letX 6156 13 J3D.nX (wordT 6156 13 J3.l4J J3D.NO J3D.NL)
      (wordT 6156 13 J3.l4J J3D.NO J3D.BZIL)) J3D.UO J3D.UL 1 :=
    j3bFaith.eq _ _ mB (wordR_M j3bFaith hXl _ _) fun b hb => by
      obtain ⟨c, hc, rfl⟩ := getD_memJ hb
      rw [Nat.eq_of_beq_eq_true (hgc c hc).2, hU 1 _ (hcs c hc)]
  have hXgen : P ≤ Subgroup.closure X := by
    rw [hPd]
    unfold subP
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · rw [hAeq]
      exact (wordT_mem hsz hX _).2
    · rw [Set.mem_singleton_iff.mp hz, hBeq]
      exact (wordT_mem hsz hX _).2
  have hcK := J3.comp
  unfold compMK at hcK
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hcK
  obtain ⟨c1, c2, c3⟩ := hcK
  have hinv : ∀ a < J3D.N, a ≠ 0 → permOfArr 6156 (unpack 6156 13 (T a)) *
      permOfArr 6156 (unpack 6156 13 (T a)) = 1 → bitK J3D.INV a = true := by
    intro a ha ha0 e
    have h := CFSG.KS.Raw.Orb.allN_iff.1 c1 a ha
    cases hb : bitK J3D.INV a
    · have e' : Nat.beq (mtI J3D.N J3D.BMT a a) (nat_lit 0) = true := (k0 ha).2 e
      rw [hb, e'] at h
      have h' : Nat.beq a (nat_lit 0) = true := h
      exact absurd (Nat.eq_of_beq_eq_true h') ha0
    · rfl
  have hFM : ∀ a < J3D.N, ∀ i, (J3D.FM a).testBit i = true →
      i < J3D.m ∧ (a = J3D.PX i ∨ a = J3D.PY i ∨ a = J3D.PXY i) := by
    intro a ha i hbit
    have h := CFSG.KS.Raw.Orb.allN_iff.1 c2 a ha
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨hlt, hall⟩ := h
    have hlt' : J3D.FM a < 2 ^ J3D.m := by
      have : J3D.FM a < 1 <<< J3D.m := Nat.blt_eq.mp hlt
      rwa [Nat.one_shiftLeft] at this
    have him : i < J3D.m := by
      by_contra hc
      have : J3D.FM a < 2 ^ i := lt_of_lt_of_le hlt' (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_eq_false_of_lt this] at hbit
      exact Bool.noConfusion hbit
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 hall i him
    rw [(bitK_iff _ _).2 hbit] at h2
    exact ⟨him, tri_of h2⟩
  have hComplete : ∀ u v : Equiv.Perm (Fin 6156), u ∈ K → v ∈ K → u ≠ 1 → v ≠ 1 → u ≠ v →
      u * u = 1 → v * v = 1 → u * v = v * u → ∃ i < J3D.m,
        (u = permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) ∨
          u = permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) ∨
          u = permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) *
            permOfArr 6156 (unpack 6156 13 (T (J3D.PY i)))) ∧
        (v = permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) ∨
          v = permOfArr 6156 (unpack 6156 13 (T (J3D.PY i))) ∨
          v = permOfArr 6156 (unpack 6156 13 (T (J3D.PX i))) *
            permOfArr 6156 (unpack 6156 13 (T (J3D.PY i)))) := by
    intro u v hu hv hu1 hv1 huv huu hvv hcomm
    obtain ⟨a, ha, rfl⟩ := hex u hu
    obtain ⟨b, hb, rfl⟩ := hex v hv
    have ha0 : a ≠ 0 := fun e => hu1 (by rw [e, hT0'])
    have hb0 : b ≠ 0 := fun e => hv1 (by rw [e, hT0'])
    have hab : Nat.beq a b = false := by
      cases e : Nat.beq a b
      · rfl
      · exact absurd (by rw [Nat.eq_of_beq_eq_true e]) huv
    have bA := hinv a ha ha0 huu
    have bB := hinv b hb hb0 hvv
    have h := CFSG.KS.Raw.Orb.allN_iff.1 c3 a ha
    rw [bA] at h
    simp only [CFSG.KS.Raw.Orb.strictB_eq] at h
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h b hb
    rw [bB, hab, (cm ha hb).2 hcomm] at h2
    have hpos : 0 < Nat.land (J3D.FM a) (J3D.FM b) := Nat.blt_eq.mp h2
    obtain ⟨i, hi⟩ : ∃ i, (Nat.land (J3D.FM a) (J3D.FM b)).testBit i = true := by
      by_contra hno
      push Not at hno
      have h0 : Nat.land (J3D.FM a) (J3D.FM b) = 0 :=
        Nat.eq_of_testBit_eq fun i => by simpa [Nat.zero_testBit] using hno i
      omega
    have hi' : (J3D.FM a).testBit i = true ∧ (J3D.FM b).testBit i = true := by
      change (J3D.FM a &&& J3D.FM b).testBit i = true at hi
      rw [Nat.testBit_and, Bool.and_eq_true] at hi
      exact hi
    obtain ⟨him, ea⟩ := hFM a ha i hi'.1
    obtain ⟨-, eb⟩ := hFM b hb i hi'.2
    obtain ⟨-, -, -, -, -, -, -, -, -, exy⟩ := hKl i him
    refine ⟨i, him, ?_, ?_⟩
    · rcases ea with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr exy.symm)
    · rcases eb with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr exy.symm)
  refine ⟨K, hKP, hcard.trans hN, ⟨{
    m := J3D.m
    nBig := J3D.nBig
    x := fun i => permOfArr 6156 (unpack 6156 13 (T (J3D.PX i)))
    y := fun i => permOfArr 6156 (unpack 6156 13 (T (J3D.PY i)))
    par := J3D.PAR
    X := X
    nBig_pos := hnb
    nBig_le := hnm
    mem_P := fun i hi => ⟨hKP (hmem _ (hKl i hi).1), hKP (hmem _ (hKl i hi).2.1)⟩
    klein := fun i hi => by
      obtain ⟨-, -, -, h1, h2, h3, h4, h5, h6, -⟩ := hKl i hi
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    complete := hComplete
    tree := hTree
    iso := hIso
    X_mem := by
      rintro _ ⟨k, hk, rfl⟩
      exact (wordT_mem hsz h4 k).2
    X_gen := hXgen
    X_norm := by
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨hj, -, e1, e2⟩ := hNorm k hk
      exact ⟨J3D.NJ k, hj, e1, e2⟩ }⟩⟩

end CertificateChecks.KernelFourJ.J3B

end
