module

public import Certificates.Kernel.LocalComp.Sp6Root.Checks
public import Certificates.Kernel.LocalComp.Sp6J.Facts
public import CFSG.Certificates.Kernel.Sp6RootSound
public import CFSG.Certificates.Kernel.SporSch.ChainKRepsL
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6RootClassInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Sp6Root

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KS.M11 CFSG.KS.MEnum CFSG.EvenSmallLie.Sp6
open CFSG.Certificates.Native CFSG.ComponentClassification.M12Cover CFSG.KS.Sp6Root
open CFSG.KS.SporSch.ClsSpec CertificateChecks.KernelLC.Sp6J

theorem h36 : (36 : Nat) < 2 ^ 32 := by norm_num

theorem hgC2 : ∀ j < sp6CentGens2.length,
    imageList (sp6CentGens2.getD j 1) = (unpack 36 6 (C2Q.S j)).toList :=
  cent_img kG2

theorem hpC2 : ∀ j < sp6CentGens2.length,
    permOK 36 6 (mask 6) (36 * 6) (C2Q.S j) (C2Q.SI j) = true :=
  fun j hj => allN_spec kP2 j hj

theorem hL : lettersK 3 [1, 1, 1, 1] = true ∧ lettersK 3 [1, 1, 2, 1, 1, 2] = true := by
  have h := ch1027001L
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem img1 : imageList (sp6SylowP1 ()) = (unpack 36 6 P1K).toList :=
  evalCodes_img kSz hgC2 hpC2 one36 hL.1

theorem img2 : imageList (sp6SylowP2 ()) = (unpack 36 6 P2K).toList :=
  evalCodes_img kSz hgC2 hpC2 one36 hL.2

theorem c1 : canonK 36 6 (mask 6) (36 * 6) P1K = true ∧
    ordIs 36 6 (mask 6) (pidn 36 6) P1K (3 - 1) = true := by
  have h := ch1027001p1
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem c2 : canonK 36 6 (mask 6) (36 * 6) P2K = true ∧
    ordIs 36 6 (mask 6) (pidn 36 6) P2K (3 - 1) = true := by
  have h := ch1027001p2
  rw [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem sylow : sp6SylowCheck () = true := by
  simp only [sp6SylowCheck, Bool.and_eq_true]
  exact ⟨⟨ordTest_of_ordIs' kSz img1 c1.1 (by norm_num) c1.2,
    ordTest_of_ordIs' kSz img2 c2.1 (by norm_num) c2.2⟩, commT_of_commK' img1 img2 ch1027001c⟩

theorem pr1 : PRep 36 6 P1K (sp6SylowP1 ()) := prep_of_imageList img1

theorem pr2 : PRep 36 6 P2K (sp6SylowP2 ()) := prep_of_imageList img2

theorem o1 : sp6SylowP1 () ^ 3 = 1 := by
  rw [← ordIs_orderOf kSz pr1 (PF.canon_facts c1.1).2.2.1 (by norm_num) c1.2]
  exact pow_orderOf_eq_one _

theorem o2 : sp6SylowP2 () ^ 3 = 1 := by
  rw [← ordIs_orderOf kSz pr2 (PF.canon_facts c2.1).2.2.1 (by norm_num) c2.2]
  exact pow_orderOf_eq_one _

theorem comm12 : Commute (sp6SylowP1 ()) (sp6SylowP2 ()) := by
  have h := commT_of_commK' img1 img2 ch1027001c
  rw [commT_eq (rep_toTable h36 _) (rep_toTable h36 _)] at h
  have h' : sp6SylowP1 () * sp6SylowP2 () = sp6SylowP2 () * sp6SylowP1 () := of_decide_eq_true h
  exact h'

theorem range9 {α : Type} (f : Nat → Nat → α) :
    ((List.range 3).flatMap fun i => (List.range 3).map fun j => f i j) =
      [f 0 0, f 0 1, f 0 2, f 1 0, f 1 1, f 1 2, f 2 0, f 2 1, f 2 2] := by
  simp [List.range_succ]

theorem perms_eq : sp6SylowPerms () =
    [sp6SylowP1 () ^ 0 * sp6SylowP2 () ^ 0, sp6SylowP1 () ^ 0 * sp6SylowP2 () ^ 1,
      sp6SylowP1 () ^ 0 * sp6SylowP2 () ^ 2, sp6SylowP1 () ^ 1 * sp6SylowP2 () ^ 0,
      sp6SylowP1 () ^ 1 * sp6SylowP2 () ^ 1, sp6SylowP1 () ^ 1 * sp6SylowP2 () ^ 2,
      sp6SylowP1 () ^ 2 * sp6SylowP2 () ^ 0, sp6SylowP1 () ^ 2 * sp6SylowP2 () ^ 1,
      sp6SylowP1 () ^ 2 * sp6SylowP2 () ^ 2] :=
  range9 fun i j => sp6SylowP1 () ^ i * sp6SylowP2 () ^ j

theorem pq (i j : Nat) : PRep 36 6 (pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P1K i)
    (powK 36 6 (mask 6) (pidn 36 6) P2K j)) (sp6SylowP1 () ^ i * sp6SylowP2 () ^ j) :=
  prep_pcomp h36 (prep_powK kSz pr1 i).1 (prep_powK kSz pr2 j).1

theorem sylF : List.Forall₂ (fun Q q => PRep 36 6 Q q) SylQ (sp6SylowPerms ()) := by
  rw [beq_iff_eq.1 ch1027001syl, perms_eq, sylSpec]
  exact .cons (pq 0 0) (.cons (pq 0 1) (.cons (pq 0 2) (.cons (pq 1 0) (.cons (pq 1 1)
    (.cons (pq 1 2) (.cons (pq 2 0) (.cons (pq 2 1) (.cons (pq 2 2) .nil))))))))

theorem cube_ij {G : Type*} [Group G] {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : Commute a b) (i j : Nat) : a ^ i * b ^ j * (a ^ i * b ^ j) = (a ^ i * b ^ j)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_three', (hab.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j,
    pow_mul, pow_mul, ha, hb, one_pow, one_pow, one_mul]

theorem cube : ∀ q ∈ sp6SylowPerms (), q * q = q⁻¹ := by
  rw [perms_eq]
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact cube_ij o1 o2 comm12 _ _

@[expose] noncomputable def qK1 (x : Equiv.Perm (Fin 36)) : Bool :=
  decide (orderOf x = 2) && commAllB (sp6SylowPerms ()) x

theorem k1Test_eq {T : Table} {x : Equiv.Perm (Fin 36)} (hT : Rep 36 T x) :
    sp6K1Test (sp6SylowTabs ()) T = qK1 x := by
  rw [sp6K1Test, sp6SylowTabs, qK1, commAllB, List.all_map]
  congr 1
  · exact Bool.eq_iff_iff.2 ((ordTest_iff perm_faithful hT (by norm_num)).trans
      decide_eq_true_iff.symm)
  · congr 1
    funext g
    exact commT_eq hT (rep_conjT (rep_toTable h36 g) (rep_toTable h36 g⁻¹) hT)

theorem hp : ∀ P x, PRep 36 6 P x → P >>> (36 * 6) = 0 →
    k1P 36 6 (mask 6) (pidn 36 6) SylQ P = qK1 x :=
  fun _ _ hP sP => k1P_eq kSz sylF cube hP sP

theorem cq2_eq : sp6CentQ2 = certificate (by decide) sp6CentGens2 q2Words
    (#v[0, 1, 4, 2] : Vector (Fin 36) 4) (by decide) := rfl

theorem k1_eq : sp6K1Count () = enumFrom 36 6 (mask 6) (36 * 6) C2Q.LR C2Q.TR
    (k1P 36 6 (mask 6) (pidn 36 6) SylQ) 4 0 One36 0 := by
  have hc := enumFrom_spec chainC2 (q := qK1) hp 4 0 (by norm_num) One36 1 0
    (prep_of_imageList one36) (by unfold One36; exact PF.pidn_shr (by norm_num) (by norm_num))
  simp only [Nat.zero_add] at hc
  rw [hc, sp6K1Count, countProducts_spec (P := fun x => qK1 x = true)
    (fun T x hT => by rw [k1Test_eq hT]) (forall₂_levelTables h36 _) (rep_toTable h36 1), cq2_eq,
    finRange_levelTransversals chainC2 (by norm_num) (by decide)]
  simp only [Bool.decide_eq_true]

theorem k1 : sp6K1Count () ≤ 7 := by
  rw [k1_eq]
  exact Nat.le_of_ble_eq_true ch1027001k1

theorem listTables_rep : ∀ l < (listTables sp6Gens).size,
    Rep 36 (listTables sp6Gens)[l]! (sp6Gens.getD l 1) ∧
      Rep 36 (listTables (sp6Gens.map (·⁻¹)))[l]! (sp6Gens.getD l 1)⁻¹ := by
  intro l hl
  have hl' : l < sp6Gens.length := by simpa [listTables] using hl
  have e1 : (listTables sp6Gens)[l]! = toTable sp6Gens[l] := by
    rw [getElem!_pos (listTables sp6Gens) l hl]
    simp [listTables]
  have e2 : (listTables (sp6Gens.map (·⁻¹)))[l]! = toTable sp6Gens[l]⁻¹ := by
    rw [getElem!_pos (listTables (sp6Gens.map (·⁻¹))) l (by simpa [listTables] using hl')]
    simp [listTables]
  have e3 : sp6Gens.getD l 1 = sp6Gens[l] := by simp [List.getD_eq_getElem?_getD, hl']
  rw [e1, e2, e3]
  exact ⟨rep_toTable h36 _, rep_toTable h36 _⟩

theorem genK_sp6 : genK (listTables sp6Gens) (fun l => sp6Gens.getD l 1) =
    Subgroup.closure ({sp6A, sp6B} : Set (Equiv.Perm (Fin 36))) := by
  unfold genK
  congr 1
  ext g
  simp only [listTables, sp6Gens, List.map_cons, List.map_nil, List.size_toArray,
    List.length_cons, List.length_nil, Nat.reduceAdd, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases l with _ | _ | l
    · simp
    · simp
    · omega
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩

theorem tA_eq : tA = imageList sp6A := by decide +kernel

theorem tB_eq : tB = imageList sp6B := by decide +kernel

theorem pR1 : PRep 36 6 D1.2.2.1 sp6Rep1 := by
  rw [Nat.eq_of_beq_eq_true ch1027001r1]
  exact prep_of_imageList (rep_img 0 (by norm_num))

theorem posS1 : 0 < D1.2.2.2.2.2.2.length := by
  have h := ch1027001ne
  rwa [Nat.blt_eq, lenN_eq'] at h

theorem hcap : (CFSG.Sporadic.SmallOddCore.conjClass
    (genK (listTables sp6Gens) (fun l => sp6Gens.getD l 1)) sp6Rep1).ncard ≤ 4000 := by
  have facts1 := datum_facts tA_eq tB_eq kSz ch1027001cls posS1 pR1
  rw [genK_sp6, facts1.1]
  exact facts1.2.1

theorem no4 : ∀ z₁ ∈ CFSG.Sporadic.SmallOddCore.conjClass
    (genK (listTables sp6Gens) (fun l => sp6Gens.getD l 1)) sp6Rep1,
    ∀ z₂ ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (genK (listTables sp6Gens) (fun l => sp6Gens.getD l 1)) sp6Rep1,
    orderOf (z₁ * z₂) ≠ 4 := by
  have facts1 := datum_facts tA_eq tB_eq kSz ch1027001cls posS1 pR1
  rw [genK_sp6]
  intro z₁ h₁ z₂ h₂
  obtain ⟨k₁, hk₁, p₁⟩ := (facts1.2.2.2.1 z₁).1 h₁
  obtain ⟨k₂, hk₂, p₂⟩ := (facts1.2.2.2.1 z₂).1 h₂
  have m₁ : D1.2.2.2.2.2.2.getD k₁ 0 ∈ S1 := by
    rw [List.getD_eq_getElem _ _ hk₁]
    exact List.getElem_mem hk₁
  have m₂ : D1.2.2.2.2.2.2.getD k₂ 0 ∈ S1 := by
    rw [List.getD_eq_getElem _ _ hk₂]
    exact List.getElem_mem hk₂
  have h := pairsK_spec 36 6 (mask 6) (pidn 36 6) S1 S1 ch1027001pairs _ m₁ _ m₂
  have e := ordIs_eq (e := 4) kSz (prep_pcomp h36 p₁ p₂) (PF.pcomp_shr _ _ h36 (by norm_num))
    (by norm_num)
  rw [show (4 : Nat) - 1 = 3 from rfl, h] at e
  intro ho
  rw [ho] at e
  exact absurd e (by decide)

theorem cl_facts {n : Nat} {gens gensInv : Array Table} {gg : Nat → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹)
    {T : Table} {y : Equiv.Perm (Fin n)} (hT : Rep n T y) {cl : List Table}
    (h1 : ∀ t ∈ cl, ∃ z ∈ CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) y, Rep n t z)
    (h2 : ∀ z ∈ CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) y, ∃ t ∈ cl, Rep n t z)
    (h4 : ∀ z₁ ∈ CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) y,
      ∀ z₂ ∈ CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) y, orderOf (z₁ * z₂) ≠ 4) :
    cl.any (tblEq n T) = true ∧
    (List.range gens.size).all (fun l => cl.all fun T' =>
      cl.any (tblEq n (conjT n gens[l]! gensInv[l]! T')) &&
        cl.any (tblEq n (conjT n gensInv[l]! gens[l]! T'))) = true ∧
    cl.all (fun T₁ => cl.all fun T₂ => !(ordTest n 4 (compT n T₁ T₂))) = true := by
  have hfind : ∀ {S : Table} {z : Equiv.Perm (Fin n)}, Rep n S z →
      z ∈ CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) y → cl.any (tblEq n S) = true := by
    intro S z hS hz
    obtain ⟨t, ht, hrt⟩ := h2 z hz
    exact List.any_eq_true.2 ⟨t, ht, (CFSG.Sporadic.SmallOddCore.tblEq_iff_eq hS hrt).2 rfl⟩
  refine ⟨hfind hT ⟨1, (genK gens gg).one_mem, by simp⟩, ?_, ?_⟩
  · refine List.all_eq_true.2 fun l hl => List.all_eq_true.2 fun T' hT' => ?_
    have hl' := List.mem_range.1 hl
    obtain ⟨z, hz, hTz⟩ := h1 T' hT'
    obtain ⟨g1, g2⟩ := hg l hl'
    have hm := gg_mem (gens := gens) (gg := gg) hl'
    rw [Bool.and_eq_true]
    refine ⟨hfind (rep_conjT g1 g2 hTz) (conj_mem_conjClass hm hz), hfind (rep_conjT g2 ?_ hTz)
      (conj_mem_conjClass ((genK gens gg).inv_mem hm) hz)⟩
    rw [inv_inv]
    exact g1
  · refine List.all_eq_true.2 fun T₁ hT₁ => List.all_eq_true.2 fun T₂ hT₂ => ?_
    obtain ⟨z₁, hz₁, r₁⟩ := h1 T₁ hT₁
    obtain ⟨z₂, hz₂, r₂⟩ := h1 T₂ hT₂
    have e := ordTest_iff perm_faithful (Rep.compT r₁ r₂) (by norm_num : 0 < 4)
    cases h : ordTest n 4 (compT n T₁ T₂)
    · rfl
    · exact absurd (e.1 h) (h4 z₁ hz₁ z₂ hz₂)

theorem ord_conj_of {r g : Equiv.Perm (Fin 36)} {R W WI : Nat} (pR : PRep 36 6 R r)
    (pW : PRep 36 6 W g) (pWI : PRep 36 6 WI g⁻¹) {e : Nat} (he : 0 < e)
    (h : ordIs 36 6 (mask 6) (pidn 36 6) (pcomp 36 6 (mask 6) R
      (pcomp 36 6 (mask 6) (pcomp 36 6 (mask 6) W R) WI)) (e - 1) = true) :
    ordTest 36 e (compT 36 (toTable r) (conjT 36 (toTable g) (toTable g⁻¹) (toTable r))) = true :=
  (ordTest_iff perm_faithful (Rep.compT (rep_toTable h36 r)
    (rep_conjT (rep_toTable h36 g) (rep_toTable h36 g⁻¹) (rep_toTable h36 r))) he).2
    (ordIs_orderOf kSz (prep_pcomp h36 pR (prep_pcomp h36 (prep_pcomp h36 pW pR) pWI))
      (PF.pcomp_shr _ _ h36 (by norm_num)) he h)

theorem hw : (lettersK 2 sp6Wit3 = true ∧ lettersK 2 sp6Wit4 = true) ∧
    (permOK 36 6 (mask 6) (36 * 6) W3K W3IK = true ∧
      permOK 36 6 (mask 6) (36 * 6) W4K W4IK = true) := by
  have h := ch1027001w
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem pW3 : PRep 36 6 W3K (evalCodes sp6Gens sp6Wit3) :=
  prep_of_imageList (evalCodes_img kSz imgX pX one36 hw.1.1)

theorem pW4 : PRep 36 6 W4K (evalCodes sp6Gens sp6Wit4) :=
  prep_of_imageList (evalCodes_img kSz imgX pX one36 hw.1.2)

theorem k2 : sp6K2Check () = true := by
  obtain ⟨-, -, h1, h2⟩ := conjClosure_spec listTables_rep (rep_toTable h36 sp6Rep1) hcap
  obtain ⟨a1, a2, a3⟩ := cl_facts listTables_rep (rep_toTable h36 sp6Rep1) h1 h2 no4
  have o3 := ord_conj_of (prep_of_imageList (rep_img 2 (by norm_num))) pW3
    (prep_inv_of_permOK pW3 hw.2.1) (by norm_num) ch1027001o3
  have o4 := ord_conj_of (prep_of_imageList (rep_img 3 (by norm_num))) pW4
    (prep_inv_of_permOK pW4 hw.2.2) (by norm_num) ch1027001o4
  simp only [sp6K2Check, sp6ClassTabs, Bool.and_eq_true]
  exact ⟨⟨⟨⟨a1, a2⟩, a3⟩, o3⟩, o4⟩

theorem facts : sp6SylowCheck () = true ∧ sp6K1Count () ≤ 7 ∧ sp6K2Check () = true :=
  ⟨sylow, k1, k2⟩

end CertificateChecks.KernelLC.Sp6Root

end
