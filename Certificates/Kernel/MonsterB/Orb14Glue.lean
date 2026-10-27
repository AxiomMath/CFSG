
module

public import Certificates.Kernel.MonsterB.Orb14GlueBase

public import Certificates.Kernel.MonsterB.Orb14EdgesS
public import Certificates.Kernel.MonsterB.Orb14EdgesN
public import CFSG.Certificates.Kernel.MonsterB.Orb14CoverSound
import all CFSG.Fischer.F4
public import Certificates.Certificate3079Base
public import CFSG.Certificates.Kernel.MonsterB.BfsReplayTSound
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CertificateChecks.Orb14

open CFSG.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census
open CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT CFSG.KC.Bfs CertificateChecks.Tau1408
open CertificateChecks.Batch3079

open CertificateChecks.Batch3079

theorem tau_ok : natCertOK genAct 17 (fun a => decide (a < 2 ^ 22)) 60 tauCert = true :=
  orbit.1

theorem tau_pts : tauCert.pts = o14VecArr := orbit.2

theorem tau_size : tauCert.pts.size = 1408 := by rw [tau_pts]; exact kSizes.2.1

theorem treeShape : TreeShape := by
  intro i h0 hi
  have h := natCertOK_tree tau_ok h0 (by rw [tau_size]; exact hi)
  exact ⟨h.1, h.2.1⟩

theorem et_spec : ∀ i < 1408, ∀ k < 17, tabE 17 11 ET i k < 1408 ∧
    o14VecArr[tabE 17 11 ET i k]! = Native.actD 22 n6RowArr[k]! o14VecArr[i]! :=
  edge_sound kSizes.2.1 kSizes.2.2.1 kTau kRow kEdge

theorem tauEdge_lt {i k : ℕ} (hi : i < 1408) (hk : k < 17) : tauEdge i k < 1408 := by
  have := (natCertOK_edge tau_ok (by rw [tau_size]; exact hi) hk).1
  rwa [tau_size] at this

theorem tauEdge_eq {i k : ℕ} (hi : i < 1408) (hk : k < 17) : tauEdge i k = tabE 17 11 ET i k := by
  obtain ⟨h1, h2⟩ := natCertOK_edge tau_ok (by rw [tau_size]; exact hi) hk
  rw [tau_pts] at h1 h2
  obtain ⟨h3, h4⟩ := et_spec i hi k hk
  exact vec_inj kDist _ h1 _ (by rw [kSizes.2.1]; exact h3) (h2.trans h4.symm)

theorem tauEdge_tree {i : ℕ} (h0 : 0 < i) (hi : i < 1408) : tauEdge (tauPar i) (tauLab i) = i := by
  have hi' : i < tauCert.pts.size := by rw [tau_size]; exact hi
  obtain ⟨hp, hl, e⟩ := natCertOK_tree tau_ok h0 hi'
  obtain ⟨h1, h2⟩ := natCertOK_edge tau_ok (hp.trans hi') hl
  exact natCertOK_inj tau_ok h1 hi' (h2.trans e.symm)

theorem tau_tree : ∀ j, 0 < j → j < 1408 → tauPar j = fget PT j 11 ∧ tauLab j = fget LT j 5 := by
  have hrep : replayTOK (tabE 17 11 ET) (fun j => fget PT j 11) (fun j => fget LT j 5) 17
      o14VecArr.size = true := by
    rw [kSizes.2.1]
    exact kRep
  have h := natBfs_tree_of_replayT (act := genAct) (fuel := 1500) (L := o14VecArr)
    (by rw [kSizes.2.1]; decide) kSizes.2.2.2 (vec_inj kDist)
    (fun i hi k hk => by rw [kSizes.2.1] at hi ⊢; exact et_spec i hi k hk) hrep
    (by rw [kSizes.2.1]; decide)
  intro j h0 hj
  exact h j h0 (by rw [kSizes.2.1]; exact hj)

theorem treeBits : TreeBits := by
  obtain ⟨a1, b1, a2, b2, a4, b4, a8, b8, a13, b13⟩ := kTree
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(tau_tree 1 (by decide) (by decide)).1, a1]
  · rw [(tau_tree 1 (by decide) (by decide)).2, b1]
  · rw [(tau_tree 2 (by decide) (by decide)).1, a2]
  · rw [(tau_tree 2 (by decide) (by decide)).2, b2]
  · rw [(tau_tree 4 (by decide) (by decide)).1, a4]
  · rw [(tau_tree 4 (by decide) (by decide)).2, b4]
  · rw [(tau_tree 8 (by decide) (by decide)).1, a8]
  · rw [(tau_tree 8 (by decide) (by decide)).2, b8]
  · rw [(tau_tree 13 (by decide) (by decide)).1, a13]
  · rw [(tau_tree 13 (by decide) (by decide)).2, b13]

theorem selEdges : SelEdges := by
  obtain ⟨a, b, c, d, e, f, g⟩ := kSelE
  exact ⟨(tauEdge_eq (by decide) (by decide)).trans a, (tauEdge_eq (by decide) (by decide)).trans b,
    (tauEdge_eq (by decide) (by decide)).trans c, (tauEdge_eq (by decide) (by decide)).trans d,
    (tauEdge_eq (by decide) (by decide)).trans e, (tauEdge_eq (by decide) (by decide)).trans f,
    (tauEdge_eq (by decide) (by decide)).trans g⟩

theorem iso_spec : b6IsoArr.size = 891 ∧ ∀ j < 891, b6IsoArr[j]! < 891 ∧ fget ISO j 10 = b6IsoArr[j]! :=
  bindL_spec (by decide) kIso

theorem frb_spec : b6FrobArr.size = 17 ∧ ∀ j < 17, b6FrobArr[j]! < 2 ∧ fget FRB j 1 = b6FrobArr[j]! :=
  bindL_spec (by decide) kFrb

theorem mat_spec : b6MatArr.size = 17 ∧ ∀ k < 17, ∀ i < 6, (b6MatArr[k]!)[i]! < 4096 ∧
    permTab 6 12 MATP i k = (b6MatArr[k]!)[i]! :=
  bindP_spec (by decide) kMat

theorem pl_spec : b6PlaneArr.size = 891 ∧ ∀ k < 891, ∀ i < 3, (b6PlaneArr[k]!)[i]! < 4096 ∧
    permTab 3 12 PLP i k = (b6PlaneArr[k]!)[i]! :=
  bindP_spec (by decide) kPl

theorem np_spec : n6PermsArr.size = 17 ∧ ∀ k < 17, ∀ i < 891, (n6PermsArr[k]!)[i]! < 891 ∧
    permTab 891 10 NP i k = (n6PermsArr[k]!)[i]! :=
  bindP_spec (by decide) kNP

theorem mem_orb {A : Array ℕ} {M : ℕ} (h : Nat.beq (bitsOf A.toList) M = true) (x : ℕ) :
    x ∈ A ↔ M.testBit x = true := by
  rw [← beq_true_iff.1 h, testBit_bitsOf, Array.mem_toList_iff]

theorem part_spec : Nat.land MO0 MO1 = 0 ∧ Nat.lor MO0 MO1 = maskN 693 ∧ Nat.land MP0 MP1 = 0 ∧
    Nat.lor MP0 MP1 = maskN 891 := by
  obtain ⟨a, b⟩ := andB_eq_true.1 kPart
  obtain ⟨b, c⟩ := andB_eq_true.1 b
  obtain ⟨c, d⟩ := andB_eq_true.1 c
  exact ⟨beq_true_iff.1 a, beq_true_iff.1 b, beq_true_iff.1 c, beq_true_iff.1 d⟩

theorem mo_split {x : ℕ} (hx : x < 693) : MO1.testBit x = !MO0.testBit x := by
  have h1 := congrArg (fun z : ℕ => z.testBit x) part_spec.1
  have h2 := congrArg (fun z : ℕ => z.testBit x) part_spec.2.1
  simp only [testBit_nland, testBit_nlor, testBit_maskN, Nat.zero_testBit, decide_eq_true hx] at h1 h2
  cases a : MO0.testBit x <;> cases b : MO1.testBit x <;> simp_all

theorem mp_split {x : ℕ} (hx : x < 891) : MP1.testBit x = !MP0.testBit x := by
  have h1 := congrArg (fun z : ℕ => z.testBit x) part_spec.2.2.1
  have h2 := congrArg (fun z : ℕ => z.testBit x) part_spec.2.2.2
  simp only [testBit_nland, testBit_nlor, testBit_maskN, Nat.zero_testBit, decide_eq_true hx] at h1 h2
  cases a : MP0.testBit x <;> cases b : MP1.testBit x <;> simp_all

theorem mo0_lt {x : ℕ} (h : MO0.testBit x = true) : x < 693 := by
  by_contra hc
  have h2 := congrArg (fun z : ℕ => z.testBit x) part_spec.2.1
  simp only [testBit_nlor, testBit_maskN, decide_eq_false hc, h, Bool.true_or] at h2
  exact absurd h2 (by decide)

theorem mn0_spec (j : ℕ) : MN0.testBit j = (decide (j < 891) && MP0.testBit (fget ISO j 10)) := by
  rw [← beq_true_iff.1 kMN0, testBit_maskB, bit_eq]

theorem singPart_get {x : ℕ} (hx : x < 693) :
    singPart[x]! = if o14PtOrb[0]!.contains x then 0 else 1 := by
  unfold singPart
  rw [getElem!_map' _ (by simpa using hx), range_get hx]

theorem natPart_get {x : ℕ} (hx : x < 891) :
    natPart[x]! = if o14PlOrb[0]!.contains (b6IsoArr[x]! % 891) then 0 else 1 := by
  unfold natPart
  rw [getElem!_map' _ (by simpa using hx), range_get hx]

theorem singPart_01 {x : ℕ} (hx : x < 693) : singPart[x]! = 0 ∨ singPart[x]! = 1 := by
  rw [singPart_get hx]
  split <;> simp

theorem natPart_01 {x : ℕ} (hx : x < 891) : natPart[x]! = 0 ∨ natPart[x]! = 1 := by
  rw [natPart_get hx]
  split <;> simp

theorem singPart_zero {x : ℕ} (hx : x < 693) : singPart[x]! = 0 ↔ MO0.testBit x = true := by
  rw [singPart_get hx, ← mem_orb kO0, ← Array.contains_iff_mem]
  cases o14PtOrb[0]!.contains x <;> simp

theorem singPart_one {x : ℕ} (hx : x < 693) : singPart[x]! = 1 ↔ MO0.testBit x = false := by
  rw [Bool.eq_false_iff, ne_eq, ← singPart_zero hx]
  rcases singPart_01 hx with h | h <;> simp [h]

theorem natPart_zero {x : ℕ} (hx : x < 891) : natPart[x]! = 0 ↔ MN0.testBit x = true := by
  rw [natPart_get hx, mn0_spec, decide_eq_true hx, Bool.true_and,
    Nat.mod_eq_of_lt (iso_spec.2 x hx).1, ← (iso_spec.2 x hx).2, ← mem_orb kP0,
    ← Array.contains_iff_mem]
  cases o14PlOrb[0]!.contains (fget ISO x 10) <;> simp

theorem natPart_one {x : ℕ} (hx : x < 891) : natPart[x]! = 1 ↔ MN0.testBit x = false := by
  rw [Bool.eq_false_iff, ne_eq, ← natPart_zero hx]
  rcases natPart_01 hx with h | h <;> simp [h]

theorem netPerm_congr {g g' : ℕ → ℕ} {N W : ℕ} (h : NetPerm g N W) (e : ∀ x < N, g x = g' x) :
    NetPerm g' N W :=
  ⟨h.ok, fun x hx => e x hx ▸ h.lt x hx, h.phi_lt, fun q hq => by
    rw [← e _ (h.phi_lt q hq)]
    exact h.g_phi q hq⟩

theorem permGens_of_net {gen : Array (Array ℕ)} {N NW : ℕ}
    (h : ∀ k < 17, NetPerm (fun x => (gen[k]!)[x]!) N (nw NW k)) : PermGens gen N :=
  ⟨fun k hk x hx => (h k hk).lt x hx, fun k hk _ hx _ hy e => (h k hk).inj hx hy e⟩

theorem netN : ∀ k < 17, NetPerm (fun x => (n6PermsArr[k]!)[x]!) 891 (nw NETN k) := by
  have h := netPerm_of_tieN kTieN (by decide) (fun k hk x hx => by
    rw [(np_spec.2 k hk x hx).2]
    exact (np_spec.2 k hk x hx).1)
  exact fun k hk => netPerm_congr (h k hk) (fun x hx => (np_spec.2 k hk x hx).2)

theorem xp_eq {c : ℕ} (hc : c < 12) : xp XP c = maskB 693 fun i => bit (fget SGL i 12) c := by
  have h : allN 12 (fun c => Nat.beq (xp XP c) (maskB 693 fun i => bit (fget SGL i 12) c)) =
    true := kXP
  rw [allN_iff] at h
  exact beq_true_iff.1 (h c hc)

theorem planes_sing (i : ℕ) (hi : i < 693) : PlanesAt XP i (singVec ⟨i, hi⟩) := by
  intro t s hs
  rw [xp_eq (by omega), testBit_maskB, decide_eq_true hi, Bool.true_and, bit_eq, ← sing_get hi]
  change _ = fb (vec6 b6SingArr[i]! t) s
  rw [fb_vec6 _ _ hs, two_mul]

theorem bit_frb {k : ℕ} (hk : k < 17) : bit FRB k = decide (b6FrobArr[k]! = 1) := by
  have e : bit FRB k = Nat.beq (fget FRB k 1) 1 := by
    change Nat.beq (Nat.land (Nat.shiftRight FRB k) 1) 1 =
      Nat.beq (Nat.land (Nat.shiftRight FRB (Nat.mul k 1)) (maskN 1)) 1
    rw [show Nat.mul k 1 = k from Nat.mul_one k]
    rfl
  rw [e, (frb_spec.2 k hk).2, Bool.eq_iff_iff, beq_true_iff, decide_eq_true_iff]

theorem imV_eq (k : ℕ) (hk : k < 17) (v : V6) :
    imV (bit FRB k) (fun r => permTab 6 12 MATP r k) v = b6Map ⟨k, hk⟩ v := by
  unfold imV b6Map
  have hm : Matrix.of (fun r : Fin 6 => vec6 (permTab 6 12 MATP r k)) = b6Mat ⟨k, hk⟩ := by
    unfold b6Mat
    exact congrArg Matrix.of (funext fun r => by rw [(mat_spec.2 k hk r r.2).2])
  have hf : barB (bit FRB k) v = barPowV (b6Frob ⟨k, hk⟩) v := by
    unfold barB barPowV b6Frob
    rw [bit_frb hk]
    rcases (by have := (frb_spec.2 k hk).1; omega : b6FrobArr[k]! = 0 ∨ b6FrobArr[k]! = 1)
      with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  rw [hm, hf]

theorem netS : ∀ k < 17, NetPerm (fun x => (singGenArr[k]!)[x]!) 693 (nw NETS k) :=
  netPerm_of_tieS kTieS planes_sing
    (fun i hi c hc => by rw [xp_eq hc, testBit_maskB, decide_eq_false (by omega), Bool.false_and])
    imV_eq sing_spec.1 (fun q hq => (sing_spec.2 q hq).1) (fun q hq => sing_nz hq) sing_nodup

theorem pgS : PermGens singGenArr 693 := permGens_of_net netS

theorem pgN : PermGens n6PermsArr 891 := permGens_of_net netN

theorem edgeOK_spec {B NW Ed o n ng N : ℕ} (h : CFSG.KC.Orb14.edgeOK B NW Ed o n ng N = true) :
    ∀ l < n, ∀ k < ng, netK (nw NW k) (fget B (o + l) N) =
      fget B (fget Ed ((o + l) * ng + k) 11) N := by
  intro l hl k hk
  rw [CFSG.KC.Orb14.edgeOK, allN_iff] at h
  have := (allN_iff _ _).1 (h l hl) k hk
  exact beq_true_iff.1 this

theorem edge_pick {B NW N : ℕ} (h : ∀ o ∈ [0, 176, 352, 528, 704, 880, 1056, 1232],
    CFSG.KC.Orb14.edgeOK B NW ET o 176 17 N = true) {i k : ℕ} (hi : i < 1408) (hk : k < 17) :
    netK (nw NW k) (fget B i N) = fget B (tabE 17 11 ET i k) N := by
  have key : ∀ o, CFSG.KC.Orb14.edgeOK B NW ET o 176 17 N = true → o ≤ i → i < o + 176 →
      netK (nw NW k) (fget B i N) = fget B (tabE 17 11 ET i k) N := by
    intro o ho h1 h2
    have := edgeOK_spec ho (i - o) (by omega) k hk
    rw [Nat.add_sub_cancel' h1] at this
    exact this
  rcases (by omega : i < 176 ∨ (176 ≤ i ∧ i < 352) ∨ (352 ≤ i ∧ i < 528) ∨ (528 ≤ i ∧ i < 704) ∨
    (704 ≤ i ∧ i < 880) ∨ (880 ≤ i ∧ i < 1056) ∨ (1056 ≤ i ∧ i < 1232) ∨ 1232 ≤ i) with
    h' | h' | h' | h' | h' | h' | h' | h'
  · exact key 0 (h 0 (by simp)) (by omega) (by omega)
  · exact key 176 (h 176 (by simp)) h'.1 (by omega)
  · exact key 352 (h 352 (by simp)) h'.1 (by omega)
  · exact key 528 (h 528 (by simp)) h'.1 (by omega)
  · exact key 704 (h 704 (by simp)) h'.1 (by omega)
  · exact key 880 (h 880 (by simp)) h'.1 (by omega)
  · exact key 1056 (h 1056 (by simp)) h'.1 (by omega)
  · exact key 1232 (h 1232 (by simp)) h' (by omega)

theorem fget_bits {X i w : ℕ} {x : ℕ} (h : (fget X i w).testBit x = true) : x < w := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (fget_lt X i w)
    (Nat.pow_le_pow_right (by decide) (by omega)))] at h
  exact absurd h (by decide)

theorem hedge_of {gen : Array (Array ℕ)} {N NW B : ℕ}
    (hg : ∀ k < 17, NetPerm (fun x => (gen[k]!)[x]!) N (nw NW k))
    (hE : ∀ i < 1408, ∀ k < 17, netK (nw NW k) (fget B i N) = fget B (tabE 17 11 ET i k) N) :
    ∀ i < 1408, ∀ k < 17, ∀ y < N, (fget B (tauEdge i k) N).testBit y = true ↔
      ∃ x < N, (gen[k]!)[x]! = y ∧ (fget B i N).testBit x = true := by
  intro i hi k hk y _
  rw [tauEdge_eq hi hk, ← hE i hi k hk, (hg k hk).netK_mask (fun x hx => fget_bits hx) y]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, fget_bits hx, e, hx⟩
  · rintro ⟨x, -, e, hx⟩
    exact ⟨x, hx, e⟩

theorem edgesS_ok : ∀ o ∈ [0, 176, 352, 528, 704, 880, 1056, 1232],
    CFSG.KC.Orb14.edgeOK SB NETS ET o 176 17 693 = true := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [eS0, eS1, eS2, eS3, eS4, eS5, eS6, eS7]

theorem edgesN_ok : ∀ o ∈ [0, 176, 352, 528, 704, 880, 1056, 1232],
    CFSG.KC.Orb14.edgeOK SBN NETN ET o 176 17 891 = true := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [eN0, eN1, eN2, eN3, eN4, eN5, eN6, eN7]

theorem schS : schreierOK singGenArr singT singI singPart 693 = true := by
  have hE := fun i (hi : i < 1408) k (hk : k < 17) => edge_pick edgesS_ok hi hk
  exact schreierOK_of_sets pgS treeShape (fun x hx => singPart_01 hx)
    (fun i x => (fget SB i 693).testBit x = true)
    (fun x hx => by
      rw [beq_true_iff.1 (andB_eq_true.1 kBase).1, singPart_zero hx])
    (fun i hi k hk => tauEdge_lt hi hk) (hedge_of netS hE) (fun i h0 hi => tauEdge_tree h0 hi)

theorem schN : schreierOK n6PermsArr natT natI natPart 891 = true := by
  have hE := fun i (hi : i < 1408) k (hk : k < 17) => edge_pick edgesN_ok hi hk
  exact schreierOK_of_sets pgN treeShape (fun x hx => natPart_01 hx)
    (fun i x => (fget SBN i 891).testBit x = true)
    (fun x hx => by
      rw [beq_true_iff.1 (andB_eq_true.1 kBase).2, natPart_zero hx])
    (fun i hi k hk => tauEdge_lt hi hk) (hedge_of netN hE) (fun i h0 hi => tauEdge_tree h0 hi)

theorem sel_ok : ∀ r < o14PtSel.size, o14PtSel[r]!.1 < 1408 ∧ o14PtSel[r]!.2 < 17 := by
  rw [kSel.1]
  decide

theorem selN_ok : ∀ r < o14PlSel.size, o14PlSel[r]!.1 < 1408 ∧ o14PlSel[r]!.2 < 17 := by
  rw [kSel.2]
  decide

theorem testBit_pw2' {a x : ℕ} (h : (pw2 a).testBit x = true) : x = a := by
  rw [testBit_pw2, decide_eq_true_iff] at h
  exact h.symm

theorem selAct_lt {gen : Array (Array ℕ)} {N : ℕ} (hg : PermGens gen N) {sel : Array (ℕ × ℕ)}
    (hs : ∀ r < sel.size, sel[r]!.1 < 1408 ∧ sel[r]!.2 < 17) :
    ∀ r < sel.size, ∀ x < N, selAct gen (transArr gen N) ((transArr gen N).map invPermArr) sel r x < N := by
  intro r hr x hx
  obtain ⟨hi, hk⟩ := hs r hr
  have he := tauEdge_lt hi hk
  have hT := transArr_perm hg treeShape
  unfold selAct
  rw [getElem!_map' invPermArr (by rw [transArr_size]; exact he)]
  exact (invPermArr_spec (hT _ he) _ (hg.lt _ hk _ ((hT _ hi).lt x hx))).1

theorem reachS (root L R : ℕ) (hR : R = pw2 root) (hroot : root < 693) :
    ∀ y, (cover NETS R L).testBit y = true →
      Reach (selAct singGenArr singT singI o14PtSel) 7 root y := by
  intro y hy
  refine (cover_sound netS treeShape treeBits selEdges (kSel.1.trans rfl) L R (fun x hx => ?_) y hy).2
  subst hR
  rw [testBit_pw2' hx]
  exact ⟨hroot, Reach.root⟩

theorem reachN (root L R : ℕ) (hR : R = pw2 root) (hroot : root < 891) :
    ∀ y, (cover NETN R L).testBit y = true →
      Reach (selAct n6PermsArr natT natI o14PlSel) 7 root y := by
  intro y hy
  refine (cover_sound netN treeShape treeBits selEdges (kSel.2.trans rfl) L R (fun x hx => ?_) y hy).2
  subst hR
  rw [testBit_pw2' hx]
  exact ⟨hroot, Reach.root⟩

end CertificateChecks.Orb14

end
