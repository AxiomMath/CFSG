module

public import Certificates.Kernel.Sporadic.ONPv.Facts
public import Certificates.Kernel.Sporadic.ONPw.Words
public import Certificates.Kernel.Sporadic.ONPw.Tree0
public import Certificates.Kernel.Sporadic.ONPw.Tree1
public import Certificates.Kernel.Sporadic.ONPw.Tree2
public import Certificates.Kernel.Sporadic.ONPw.Tree3
public import CFSG.Certificates.Kernel.Spor.ONPwSurv
public import CFSG.Sporadic.Schreier.ONCentralQuotient

public noncomputable section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPw

open CFSG.KC.Enum CFSG.KS CFSG.KS.ONPw CFSG.KS.ONPv CFSG.KS.ONNQ CFSG.ONSchreier
open CertificateChecks.KernelSpor.ONPv

theorem pw_items : PwItems OPW.D := by decide +kernel

theorem items_words : wd (OPW.D 0) = Data.MWords[0]! ∧ wd (OPW.D 1) = Data.MWords[1]! ∧
    wd (OPW.D 2) = Data.MWords[2]! ∧ wd (OPW.D 3) = Data.LWords[0]! ∧
    wd (OPW.D 4) = Data.LWords[1]! ∧ wd (OPW.D 5) = Data.centerGeneratorWord := by
  decide +kernel

theorem blk_eq : ∀ k < 120, blk OPW.D k 0 = (Data.quotientBlocks[k]!)[0]! ∧
    blk OPW.D k 1 = (Data.quotientBlocks[k]!)[1]! := by
  decide +kernel

theorem blkE {k i : Nat} (hk : k < 120) (hi : i < 2) :
    blk OPW.D k i = (Data.quotientBlocks[k]!)[i]! := by
  interval_cases i
  exacts [(blk_eq k hk).1, (blk_eq k hk).2]

section Elems


theorem sI_eq {j : Nat} (hj : j < 13) {w : List Int} (hw : wd (OPW.D j) = w) :
    sI sgen OPW.D j = evalS w := by
  have hl : Lm 7 w := by
    rw [← hw]
    exact pw_items.1 j hj
  rw [evalS, evalWord_eq_wv sgen hl, sI, hw]

theorem evalS_mem_list {ws : Array (List Int)} {i : Nat} (hi : i < ws.size) :
    evalS ws[i]! ∈ evalList ws := by
  rw [getElem!_pos ws i hi]
  exact List.mem_map_of_mem (Array.getElem_mem_toList hi)

theorem sI_M {j : Nat} (hj : j < 3) : sI sgen OPW.D j ∈ onM := by
  have hw : wd (OPW.D j) = Data.MWords[j]! := by
    interval_cases j
    exacts [items_words.1, items_words.2.1, items_words.2.2.1]
  have hs : Data.MWords.size = 3 := rfl
  rw [sI_eq (by omega) hw]
  exact Subgroup.subset_closure (evalS_mem_list (ws := Data.MWords) (by omega))

theorem sI3_L : sI sgen OPW.D 3 ∈ onL := by
  have hs : Data.LWords.size = 2 := rfl
  rw [sI_eq (by omega) items_words.2.2.2.1]
  exact Subgroup.subset_closure (evalS_mem_list (ws := Data.LWords) (by omega))

theorem sI4_L : sI sgen OPW.D 4 ∈ onL := by
  have hs : Data.LWords.size = 2 := rfl
  rw [sI_eq (by omega) items_words.2.2.2.2.1]
  exact Subgroup.subset_closure (evalS_mem_list (ws := Data.LWords) (by omega))

theorem sI5 : sI sgen OPW.D 5 = onq := sI_eq (by omega) items_words.2.2.2.2.2

end Elems

section Blocks


open scoped Classical in
def rhoP (x : Equiv.Perm (Fin 245520)) : Equiv.Perm (Fin 120) :=
  if h : x ∈ onM then rhoM ⟨x, h⟩ else 1

theorem rhoP_of {x : Equiv.Perm (Fin 245520)} (h : x ∈ onM) : rhoP x = rhoM ⟨x, h⟩ := dif_pos h

theorem bpos {k i : Nat} (hk : k < 120) (hi : i < 2) :
    bPos[(Data.quotientBlocks[k]!)[i]!]! = k := by
  obtain ⟨-, -, -, -, h0, h1⟩ := blocks_wf hk
  interval_cases i
  exacts [h0, h1]

theorem sI_memM : ∀ j < 5, sI sgen OPW.D j ∈ onM := by
  intro j hj
  rcases Nat.lt_or_ge j 3 with h | h
  · exact sI_M h
  · have e : j = 3 ∨ j = 4 := by omega
    rcases e with rfl | rfl
    exacts [onL_le_M sI3_L, onL_le_M sI4_L]

theorem pw_blocks : Blocks OPW.D onM rhoP where
  mul a ha b hb := by
    rw [rhoP_of (mul_mem ha hb), rhoP_of ha, rhoP_of hb, ← map_mul]
    rfl
  lt k hk := by
    rw [blkE hk (by omega)]
    exact (blocks_wf hk).2.1
  img m hm k := by
    have hx : ((⟨m, hm⟩ : onM) : Equiv.Perm (Fin N)) ⟨_, (blocks_wf k.isLt).2.1⟩ ∈
        onBsets[(rhoM ⟨m, hm⟩ k : ℕ)]'(by rw [onBsets_length]; exact (rhoM ⟨m, hm⟩ k).isLt) := by
      rw [rhoM_spec]
      apply Set.smul_mem_smul_set
      rw [onBsets_eq_pair k.isLt]
      exact Or.inl rfl
    rw [onBsets_eq_pair (rhoM ⟨m, hm⟩ k).isLt, Set.mem_setOf_eq] at hx
    have e : ∀ h, (⟨blk OPW.D k 0, h⟩ : Fin 245520) = ⟨_, (blocks_wf k.isLt).2.1⟩ :=
      fun _ => Fin.ext (blkE k.isLt (by omega))
    rw [e, rhoP_of hm, blkE (rhoM ⟨m, hm⟩ k).isLt (by omega),
      blkE (rhoM ⟨m, hm⟩ k).isLt (by omega)]
    exact hx.imp (congrArg Fin.val) (congrArg Fin.val)
  disj k hk k' hk' i hi i' hi' h := by
    rw [blkE hk hi, blkE hk' hi'] at h
    rw [← bpos hk hi, h, bpos hk' hi']


theorem rhoP_image : rhoP '' (onL : Set (Equiv.Perm (Fin 245520))) =
    (rhoL.range : Set (Equiv.Perm (Fin 120))) := by
  ext σ
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact MonoidHom.mem_range.2 ⟨⟨l, hl⟩, (rhoP_of (onL_le_M hl)).symm⟩
  · intro h
    obtain ⟨l, rfl⟩ := MonoidHom.mem_range.1 h
    exact ⟨l, l.2, rhoP_of (onL_le_M l.2)⟩


theorem pw_card : (rhoP '' (onL : Set (Equiv.Perm (Fin 245520)))).ncard = 20160 := by
  rw [rhoP_image, ← Nat.card_coe_set_eq]
  exact card_rhoL_range

theorem pw_ker : ∀ l ∈ onL, rhoP l = 1 → ∃ k < 4, l = sI sgen OPW.D 5 ^ k := by
  intro l hl h1
  have e : rhoL ⟨l, hl⟩ = rhoP l := (rhoP_of (onL_le_M hl)).symm
  have hk : (⟨l, hl⟩ : onL) ∈ rhoL.ker := MonoidHom.mem_ker.2 (e.trans h1)
  rw [rhoL_ker, Subgroup.mem_subgroupOf] at hk
  obtain ⟨z, hz'⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hz : onq ^ z = l := hz'
  have hm := zpow_mod_orderOf onq z
  rw [orderOf_onq] at hm
  push_cast at hm
  refine ⟨(z % 4).toNat, by omega, ?_⟩
  rw [sI5, ← hz, ← zpow_natCast, Int.toNat_of_nonneg (by omega), hm]

end Blocks

theorem pw_nodes : ∀ i < 20160, nodeOK OPW.D i = true := by
  have hs : ∀ s < 16, nodesOK OPW.D (1260 * s) 1260 = true := by
    intro s hs
    interval_cases s
    exacts [pw_t0, pw_t1, pw_t2, pw_t3, pw_t4, pw_t5, pw_t6, pw_t7, pw_t8, pw_t9, pw_t10, pw_t11,
      pw_t12, pw_t13, pw_t14, pw_t15]
  intro i hi
  have h : nodeOK OPW.D (Nat.add (1260 * (i / 1260)) (i % 1260)) = true :=
    allN_spec (hs (i / 1260) (by omega)) (i % 1260) (Nat.mod_lt _ (by omega))
  rwa [show Nat.add (1260 * (i / 1260)) (i % 1260) = i from Nat.div_add_mod i 1260] at h

theorem pw_treeH :
    TreeH CertificateChecks.KernelSpor.ON.TT CertificateChecks.KernelSpor.ON.UU OPW.D sgen onM onL
      rhoP where
  rp := rp_on
  items := pw_items
  blk := pw_blocks
  memM := sI_memM
  rho := pw_rho
  le := onL_le_M
  memL3 := sI3_L
  memL4 := sI4_L
  card := pw_card
  ker := pw_ker
  nodes := pw_nodes

end CertificateChecks.KernelSpor.ONPw

end
