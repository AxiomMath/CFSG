module

public import Certificates.Kernel.Fi22Cover.Checks
public import Certificates.Kernel.Sporadic.Fi22.C2079A
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiAmb
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.RankThree.Native.PermEnumeration
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiMain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Cover

open CFSG.KC.Fi22Cover CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.HardMathSupport.Solomon.Coordinator CertificateChecks.KernelSpor CFSG.Open
open CFSG.Certificates

noncomputable abbrev pp (p : Nat) : Equiv.Perm (Fin 3510) := permOfArr 3510 (unpack 3510 12 p)

theorem prep_pp {p q : Nat} (h : permOK 3510 12 (mask 12) (3510 * 12) p q = true) :
    PRep 3510 12 p (pp p) ∧ PRep 3510 12 q (pp p)⁻¹ := by
  have hr := rep_permOfArr (isInvA_unpack h)
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

theorem prep_eq {P : Nat} {g h : Equiv.Perm (Fin 3510)} (hg : PRep 3510 12 P g)
    (hh : PRep 3510 12 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_c {p q : Nat} {g h : Equiv.Perm (Fin 3510)} (hp : PRep 3510 12 p g)
    (hq : PRep 3510 12 q h) : PRep 3510 12 (c p q) (g * h) :=
  prep_pcomp (by norm_num) hp hq

theorem prep_id : PRep 3510 12 idP 1 := prep_pidn (by norm_num) (by norm_num)

theorem bAnd_split {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem inT_spec {N : Nat} {T : Nat → Nat} {x : Nat} (h : inT N T x = true) :
    ∃ j < N, x = T j := by
  induction N with
  | zero =>
    have h' : false = true := h
    exact absurd h' (by decide)
  | succ N ih =>
    have h' : bIf(Nat.beq x (T N), true, inT N T x) = true := h
    cases hb : Nat.beq x (T N) with
    | true => exact ⟨N, by omega, Nat.eq_of_beq_eq_true hb⟩
    | false =>
      rw [hb] at h'
      obtain ⟨j, hj, e⟩ := ih h'
      exact ⟨j, by omega, e⟩

theorem prepS {j : Nat} (hj : j < 20) : PRep 3510 12 (S j) (pp (S j)) ∧
    PRep 3510 12 (SI j) (pp (S j))⁻¹ :=
  prep_pp (allN_spec permS j hj)

theorem siftS_spec {j : Nat} (hj : j < 3) :
    cn (S j) = true ∧ pk (S j) = true ∧ siftP (S j) = true := by
  obtain ⟨h1, h2⟩ := bAnd_split (allN_spec siftS j hj)
  exact ⟨h1, bAnd_split h2⟩

theorem siftE_spec {k : Nat} (hk : k < 5) :
    cn (E5B.G k) = true ∧ pk (E5B.G k) = true ∧ siftP (E5B.G k) = true := by
  obtain ⟨h1, h2⟩ := bAnd_split (allN_spec siftE k hk)
  exact ⟨h1, bAnd_split h2⟩

theorem siftQ_spec {k : Nat} (hk : k < 4) :
    cn (Q4B.G k) = true ∧ pk (Q4B.G k) = true ∧ siftP (Q4B.G k) = true := by
  obtain ⟨h1, h2⟩ := bAnd_split (allN_spec siftQ k hk)
  exact ⟨h1, bAnd_split h2⟩

theorem prep_inv {p : Nat} (h : pk p = true) : PRep 3510 12 (inv p) (pp p)⁻¹ :=
  (prep_pp (q := inv p) h).2

theorem mem_P' {p : Nat}
    (h : cn p = true ∧ pk p = true ∧ siftP p = true) : pp p ∈ fi22P :=
  Fo22C.mem_P (q := inv p) h.1 h.2.2 h.2.1

noncomputable abbrev H3 : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {pp (S 0), pp (S 1), pp (S 2)}

theorem word_prep {j : Nat} (hj : j ≤ 20) {w : List Nat} (hl : lt w j = true) :
    PRep 3510 12 (wd S SI w)
      (Quiver.SchreierGraph.evalWord (fun h : Fin j => pp (S h)) (toLetters j (w.map toInt))) :=
  (prep_wordK (n := 3510) (by norm_num) (by norm_num) (gs := fun h => pp (S h))
    (fun h hh => (prepS (by omega)).1) (fun h hh => (prepS (by omega)).2) _ hl).1

theorem gS_mem : ∀ j < 20, pp (S j) ∈ H3 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h3 : j < 3
    · refine Subgroup.subset_closure ?_
      interval_cases j <;> simp
    · have hd := allN_spec der (j - 3) (by omega)
      rw [Nat.add_eq, Nat.sub_add_cancel (by omega)] at hd
      obtain ⟨hl, he⟩ := bAnd_split hd
      rw [prep_eq (prepS hj).1 (by rw [Nat.eq_of_beq_eq_true he]; exact word_prep (by omega) hl)]
      refine (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
      rintro _ ⟨h, rfl⟩
      exact ih h.val (by omega) (by omega)

theorem gen_mem {k : Nat} (hk : k < 2) : fi22GenPerm k ∈ H3 := by
  obtain ⟨hl, he⟩ := bAnd_split (allN_spec wa k hk)
  have hr := rep_fi22Gen hk
  rw [Fi22G.gen_eq hk] at hr
  rw [prep_eq (prep_of_rep hr) (by rw [Nat.eq_of_beq_eq_true he]; exact word_prep le_rfl hl)]
  refine (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact gS_mem h.val h.isLt

theorem fi22P_eq' : fi22P = Subgroup.closure (Set.range fun k : Fin 2 => fi22GenPerm k) := by
  rw [fi22P, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  change g ∈ (Vector.ofFn fun k : Fin 2 => fi22GenPerm k).toList ↔ _
  rw [Vector.toList_ofFn, List.mem_ofFn, Set.mem_range]

theorem gen_eq_P : H3 = fi22P := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [mem_P' (siftS_spec (by norm_num)), mem_P' (siftS_spec (by norm_num)),
      mem_P' (siftS_spec (by norm_num))]
  · rw [fi22P_eq', Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact gen_mem k.isLt

noncomputable abbrev gsOf (ng : Nat) (G : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := ng) fun k => unpack 3510 12 (G k.val)

theorem gsOf_get {ng : Nat} {G : Nat → Nat} {k : Nat} (hk : k < ng) :
    (gsOf ng G)[k]! = unpack 3510 12 (G k) := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem hps : ∀ p ∈ List.range 3510, p < 3510 := fun p hp => List.mem_range.1 hp

theorem enum_facts {ng N : Nat} {G T E SS : Nat → Nat} (hk : bfsK 3510 12 ng G N T E SS = true)
    (hp : ∀ k < ng, pk (G k) = true) :
    Nat.card (Subgroup.closure (permsA 3510 (gsOf ng G))) = N ∧
      (∀ j < N, ∀ x, PRep 3510 12 (T j) x → x ∈ Subgroup.closure (permsA 3510 (gsOf ng G))) ∧
      permsA 3510 (gsOf ng G) = (fun k => pp (G k)) '' {k | k < ng} := by
  have hs : (gsOf ng G).size = ng := Array.size_ofFn
  have hg : ∀ k < ng, (gsOf ng G)[k]! = unpack 3510 12 (G k) := fun k hk => gsOf_get hk
  have hc := enumOK_of_bfsK hs hg hp hk le_rfl
  have hpts := enumBfs_pts hs hg hk le_rfl
  have hspec := enumOK_spec hps hc
  refine ⟨by rw [hspec.2.1, hpts, Array.size_ofFn], fun j hj x hx => ?_, ?_⟩
  · refine enumOK_mem_of_mem hps hc (rep_unpack hx) ?_
    rw [hpts, Array.toList_ofFn, List.mem_ofFn]
    exact ⟨⟨j, hj⟩, rfl⟩
  · ext x
    simp only [permsA, Set.mem_image, Set.mem_setOf_eq, hs]
    constructor <;> rintro ⟨k, hk, rfl⟩ <;> exact ⟨k, hk, by rw [gsOf_get hk]⟩

theorem conj_mem {n ng N : Nat} {G T : Nat → Nat} {gn : Equiv.Perm (Fin 3510)}
    {gG : Nat → Equiv.Perm (Fin 3510)} {K : Subgroup (Equiv.Perm (Fin 3510))}
    (hn : PRep 3510 12 n gn) (hni : PRep 3510 12 (inv n) gn⁻¹)
    (hG : ∀ k < ng, PRep 3510 12 (G k) (gG k))
    (hT : ∀ j < N, ∀ x, PRep 3510 12 (T j) x → x ∈ K) (h : conjK n ng G N T = true) {k : Nat}
    (hk : k < ng) : gn * gG k * gn⁻¹ ∈ K ∧ gn⁻¹ * gG k * gn ∈ K := by
  obtain ⟨h1, h2⟩ := bAnd_split (allN_spec h k hk)
  obtain ⟨j1, hj1, e1⟩ := inT_spec h1
  obtain ⟨j2, hj2, e2⟩ := inT_spec h2
  refine ⟨hT j1 hj1 _ ?_, hT j2 hj2 _ ?_⟩
  · rw [← e1]
    exact prep_c (prep_c hn (hG k hk)) hni
  · rw [← e2]
    exact prep_c (prep_c hni (hG k hk)) hn

theorem normalizer_of {n ng N : Nat} {G T : Nat → Nat} {gn : Equiv.Perm (Fin 3510)}
    (hn : PRep 3510 12 n gn) (hni : PRep 3510 12 (inv n) gn⁻¹)
    (hG : ∀ k < ng, PRep 3510 12 (G k) (pp (G k)))
    (hT : ∀ j < N, ∀ x, PRep 3510 12 (T j) x →
      x ∈ Subgroup.closure ((fun k => pp (G k)) '' {k | k < ng}))
    (h : conjK n ng G N T = true) :
    gn ∈ Subgroup.normalizer
      ((Subgroup.closure ((fun k => pp (G k)) '' {k | k < ng}) :
        Subgroup (Equiv.Perm (Fin 3510))) : Set (Equiv.Perm (Fin 3510))) := by
  refine fi_normalizer_closure (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨k, hk, rfl⟩ := hs
    exact (conj_mem hn hni hG hT h hk).1
  · obtain ⟨k, hk, rfl⟩ := hs
    exact (conj_mem hn hni hG hT h hk).2

theorem elem_of {ng : Nat} {G : Nat → Nat} (hG : ∀ k < ng, PRep 3510 12 (G k) (pp (G k)))
    (h : elemK ng G = true) :
    IsElemAbelian 3 (Subgroup.closure ((fun k => pp (G k)) '' {k | k < ng})) := by
  refine fi_elemAbelian_closure ?_ ?_
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    have h2 := allN_spec (bAnd_split (allN_spec h i hi)).2 j hj
    exact prep_eq (prep_c (hG i hi) (hG j hj))
      (by rw [Nat.eq_of_beq_eq_true h2]; exact prep_c (hG j hj) (hG i hi))
  · rintro _ ⟨i, hi, rfl⟩
    have h1 := (bAnd_split (allN_spec h i hi)).1
    rw [pow_three]
    exact prep_eq (prep_c (hG i hi) (prep_c (hG i hi) (hG i hi)))
      (by rw [Nat.eq_of_beq_eq_true h1]; exact prep_id)

noncomputable abbrev E5 : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure ((fun k => pp (E5B.G k)) '' {k | k < 5})

noncomputable abbrev Q4 : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure ((fun k => pp (Q4B.G k)) '' {k | k < 4})

theorem hGE {k : Nat} (hk : k < 5) : PRep 3510 12 (E5B.G k) (pp (E5B.G k)) :=
  (prep_pp (siftE_spec hk).2.1).1

theorem hGQ {k : Nat} (hk : k < 4) : PRep 3510 12 (Q4B.G k) (pp (Q4B.G k)) :=
  (prep_pp (siftQ_spec hk).2.1).1

theorem factsE : Nat.card E5 = 3 ^ 5 ∧ ∀ j < E5B.N, ∀ x, PRep 3510 12 (E5B.T j) x → x ∈ E5 := by
  have hng : E5B.ng = 5 := rfl
  obtain ⟨hc, hm, he⟩ := enum_facts E5B.ok fun k hk => (siftE_spec (hng ▸ hk)).2.1
  rw [he, hng] at hc hm
  exact ⟨hc, hm⟩

theorem factsQ : Nat.card Q4 = 3 ^ 4 ∧ ∀ j < Q4B.N, ∀ x, PRep 3510 12 (Q4B.T j) x → x ∈ Q4 := by
  have hng : Q4B.ng = 4 := rfl
  obtain ⟨hc, hm, he⟩ := enum_facts Q4B.ok fun k hk => (siftQ_spec (hng ▸ hk)).2.1
  rw [he, hng] at hc hm
  exact ⟨hc, hm⟩

theorem fi22CoverData_kernel :
    Fi22CoverData ↥fi22P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcE, hmE⟩ := factsE
  obtain ⟨hcQ, hmQ⟩ := factsQ
  have hE5M : E5 ≤ fi22P := (Subgroup.closure_le _).2 (by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_P' (siftE_spec hk))
  have hQ4M : Q4 ≤ fi22P := (Subgroup.closure_le _).2 (by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_P' (siftQ_spec hk))
  have hQE : Q4 ≤ Subgroup.normalizer (E5 : Set (Equiv.Perm (Fin 3510))) :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨k, hk, rfl⟩
      exact normalizer_of (hGQ hk) (prep_inv (siftQ_spec hk).2.1) (fun i hi => hGE hi) hmE
        (allN_spec normQE k hk))
  have hpEQ : IsPGroup 3 (E5 ⊔ Q4 : Subgroup (Equiv.Perm (Fin 3510))) :=
    (IsPGroup.of_card hcE).to_sup_of_normal_left' (IsPGroup.of_card hcQ) hQE
  obtain ⟨Q, hQ⟩ := (hpEQ.comap_of_injective fi22P.subtype fi22P.subtype_injective).exists_le_sylow
  have hcP0 : Nat.card ((Q : Subgroup ↥fi22P).map fi22P.subtype) = Nat.card Q :=
    Subgroup.card_map_of_injective fi22P.subtype_injective
  have hsub : E5 ⊔ Q4 ≤ (Q : Subgroup ↥fi22P).map fi22P.subtype := fun x hx =>
    ⟨⟨x, sup_le hE5M hQ4M hx⟩, hQ hx, rfl⟩
  have hn5 := siftS_spec (j := 0) (by norm_num)
  have hn4 := siftS_spec (j := 1) (by norm_num)
  have hn4' := siftS_spec (j := 2) (by norm_num)
  refine fi22CoverData_of_ambient fi22P ((Q : Subgroup ↥fi22P).map fi22P.subtype) E5 Q4
    (pp (S 0)) (pp (S 1)) (pp (S 2)) (Subgroup.map_subtype_le _)
    (IsPGroup.of_card (hcP0.trans Q.card_eq_multiplicity)) (hcP0.trans Q.card_eq_multiplicity)
    (le_sup_left.trans hsub) (elem_of (fun k hk => hGE hk) elemE) hcE
    (le_sup_right.trans hsub) (elem_of (fun k hk => hGQ hk) elemQ) hcQ
    (mem_P' hn5) (mem_P' hn4) (mem_P' hn4')
    (normalizer_of (prepS (by norm_num)).1 (prep_inv hn5.2.1) (fun i hi => hGE hi) hmE normE)
    (normalizer_of (prepS (by norm_num)).1 (prep_inv hn4.2.1) (fun i hi => hGQ hi) hmQ normQ)
    (normalizer_of (prepS (by norm_num)).1 (prep_inv hn4'.2.1) (fun i hi => hGQ hi) hmQ normQ')
    gen_eq_P

end CertificateChecks.KernelFi22Cover

end
