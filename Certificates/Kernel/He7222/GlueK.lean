module

public import Certificates.Kernel.He7222.GlueScan
public import Certificates.Kernel.He7222.KBndK
public import CFSG.Certificates.Kernel.He7222.ChainPRepLe
public import CFSG.Certificates.Kernel.He7222.FibGrp
public import CFSG.Certificates.Kernel.He7222.KChSound
public import CFSG.Certificates.Kernel.He7222.ClsSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.OrbRow.LevelSound
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223
  CertificateChecks.KernelSchreierFam.He725 CFSG.KS.PF

theorem keyF_congr (w : ℕ) {f f' : ℕ → ℕ} : ∀ nf, (∀ k < nf, f k = f' k) →
    keyF w f nf = keyF w f' nf
  | 0, _ => rfl
  | k + 1, h => by
    change Nat.lor (keyF w f k) (Nat.shiftLeft (f k) (Nat.mul w k)) =
      Nat.lor (keyF w f' k) (Nat.shiftLeft (f' k) (Nat.mul w k))
    rw [keyF_congr w k (fun i hi => h i (by omega)), h k (by omega)]

@[expose] noncomputable def tupP (Ts : List (List ℕ)) (ix : List ℕ) : Equiv.Perm (Fin 8330) :=
  (tupL (fun t j => recP 8330 14 ((Ts.getD t []).getD j 0)) Ts.length ix).prod

theorem k_chain {τ : Equiv.Perm (Fin 8330)}
    {Ts TIs : List (List ℕ)} (hTI : TIs.length = Ts.length)
    (hrep : ∀ t < Ts.length, ∀ j < (Ts.getD t []).length,
      recP 8330 14 ((Ts.getD t []).getD j 0) ∈ centralizerIn heP τ ∧
      PRep 8330 14 ((Ts.getD t []).getD j 0) (recP 8330 14 ((Ts.getD t []).getD j 0)))
    (hshr : ∀ t < Ts.length, ∀ j < (Ts.getD t []).length,
      (Ts.getD t []).getD j 0 >>> (8330 * 14) = 0)
    (hinv : ∀ t < Ts.length,
      invLK 8330 14 (mask 14) (pidn 8330 14) (Ts.getD t []) (TIs.getD t []) = true)
    {rs : List ℕ} {sP : ℕ} {s : Equiv.Perm (Fin 8330)}
    (hrs : ∀ p : Fin 8330, evK 14 (mask 14) rs p = s p) (hsP : PRep 8330 14 sP s)
    (hs : s ∈ centralizerIn heP τ) {KC : List (List ℕ)} {keys : List ℕ}
    (hcls : clsK 14 (mask 14) Ts TIs rs KC keys = true) (hinc : keys.Pairwise (· < ·))
    {G : List ℕ} {U : List (List ℕ)}
    (hkg : kgK 8330 14 (mask 14) (pidn 8330 14) Ts sP G U = true)
    {B : List ℕ} {R T S Ref Nn : List (List ℕ)}
    (hch : chainK 8330 14 (mask 14) (pidn 8330 14) G B R T S Ref Nn = true)
    (hB : ∀ i < B.length, B.getD i 0 < 8330)
    (hn : keys.length * ∏ i ∈ Finset.range B.length, (T.getD i []).length =
      Nat.card (centralizerIn heP τ)) :
    (∀ i < B.length, ∀ j < (T.getD i []).length,
      recP 8330 14 ((T.getD i []).getD j 0) ∈ centralizerIn heP τ ⊓ Subgroup.centralizer {s} ∧
      PRep 8330 14 ((T.getD i []).getD j 0) (recP 8330 14 ((T.getD i []).getD j 0))) ∧
    (∀ g ∈ centralizerIn heP τ ⊓ Subgroup.centralizer {s}, ∃ f : ℕ → ℕ,
      (∀ i < B.length, f i < (T.getD i []).length) ∧
      g = ((List.range B.length).map fun i => recP 8330 14 ((T.getD i []).getD (f i) 0)).prod) ∧
    ∀ z ∈ centralizerIn heP τ, ∃ pos < KC.length,
      (tupP Ts (KC.getD pos []))⁻¹ * z ∈ centralizerIn heP τ ⊓ Subgroup.centralizer {s} := by
  set C := centralizerIn heP τ with hC
  set rec : ℕ → ℕ → Equiv.Perm (Fin 8330) := fun t j => recP 8330 14 ((Ts.getD t []).getD j 0)
    with hrec
  obtain ⟨hlenK, hall⟩ := clsK_sound hcls
  have hmem : ∀ pos < KC.length, tupP Ts (KC.getD pos []) ∈ C ∧ ∀ p : Fin 8330,
      cjEv 14 (mask 14) (stkK Ts (KC.getD pos [])) rs (stkIK TIs (KC.getD pos []) []) p =
        (tupP Ts (KC.getD pos []) * s * (tupP Ts (KC.getD pos []))⁻¹) p := by
    intro pos hpos
    obtain ⟨htup, -⟩ := hall pos hpos
    set ix := KC.getD pos [] with hix
    obtain ⟨hixl, hixb⟩ := tupOK_spec htup
    have hst := stkK_rep (n := 8330) (w := 14) rec htup (fun t ht j hj => (hrep t ht j hj).2)
    set cl := tupL rec Ts.length ix with hcl
    have hinvr : ∀ t < TIs.length, PRep 8330 14 ((TIs.getD t []).getD (ix.getD t 0) 0)
        ((fun t j => (rec t j)⁻¹) t (ix.getD t 0)) := by
      intro t ht
      have ht' : t < Ts.length := by omega
      obtain ⟨-, hi2⟩ := invLK_sound (hinv t ht')
      have hj := hixb t ht'
      exact invK_rep (by norm_num) (by norm_num) (hi2 _ hj) (hrep t ht' _ hj).2 (hshr t ht' _ hj)
    have hsti := stkIK_rep (n := 8330) (w := 14) (fun t j => (rec t j)⁻¹) (acc := [])
      (accg := []) (by omega) hinvr List.Forall₂.nil
    rw [List.append_nil, hTI] at hsti
    have hci : (tupL (fun t j => (rec t j)⁻¹) Ts.length ix).reverse.prod = cl.prod⁻¹ := by
      rw [hcl, List.prod_inv_reverse]
      simp only [tupL, List.map_map]
      rfl
    have hcP : cl.prod ∈ C := by
      refine Subgroup.list_prod_mem (K := C) fun g hg => ?_
      simp only [hcl, tupL, List.mem_map, List.mem_range] at hg
      obtain ⟨t, ht, rfl⟩ := hg
      exact (hrep t ht _ (hixb t ht)).1
    refine ⟨hcP, fun p => ?_⟩
    change evK 14 (mask 14) _ (evK 14 (mask 14) rs (evK 14 (mask 14) _ p)) = _
    rw [evK_rep hsti p, hci, hrs, evK_rep hst]
    simp only [Equiv.Perm.mul_apply]
    rfl
  have hnd : keys.Nodup := hinc.imp (fun h => ne_of_lt h)
  have hdist : ∀ i < KC.length, ∀ j < KC.length,
      tupP Ts (KC.getD i []) * s * (tupP Ts (KC.getD i []))⁻¹ =
        tupP Ts (KC.getD j []) * s * (tupP Ts (KC.getD j []))⁻¹ → i = j := by
    intro i hi j hj he
    have hk : keys.getD i 0 = keys.getD j 0 := by
      rw [← (hall i hi).2, ← (hall j hj).2]
      refine keyF_congr 14 5 fun k hk => ?_
      have e1 := (hmem i hi).2 ⟨k, by omega⟩
      have e2 := (hmem j hj).2 ⟨k, by omega⟩
      simp only at e1 e2
      rw [e1, e2, he]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hk
    exact (hnd.getElem_inj_iff).1 hk
  obtain ⟨hle3, hcomp⟩ := class_count C s (fun pos => tupP Ts (KC.getD pos []))
    (fun i hi => (hmem i hi).1) hdist
  set K := C ⊓ Subgroup.centralizer {s} with hK
  obtain ⟨hUG, hgen⟩ := kgK_sound hkg
  have h0 : ∀ q < (chainGens G S 0).length, ∃ g ∈ K, PRep 8330 14 ((chainGens G S 0).getD q 0) g := by
    intro q hq
    have e0 : chainGens G S 0 = G := by simp [chainGens]
    rw [e0] at hq ⊢
    obtain ⟨htup, htk, hcm⟩ := hgen q (by omega)
    obtain ⟨-, hixb⟩ := tupOK_spec htup
    have hp := tupK_rep (n := 8330) (w := 14) (by norm_num) (by norm_num) rec htup
      (fun t ht j hj => (hrep t ht j hj).2)
    rw [htk] at hp
    have hgC : (tupL rec Ts.length (U.getD q [])).prod ∈ C := by
      refine Subgroup.list_prod_mem (K := C) fun g hg => ?_
      simp only [tupL, List.mem_map, List.mem_range] at hg
      obtain ⟨t, ht, rfl⟩ := hg
      exact (hrep t ht _ (hixb t ht)).1
    have hc := comm_of_commK hcm hp hsP
    exact ⟨_, Subgroup.mem_inf.2 ⟨hgC, Subgroup.mem_centralizer_singleton_iff.2 hc⟩, hp⟩
  obtain ⟨hTB, hlev⟩ := chainK_sound hch
  have hpos : 0 < keys.length := by
    rcases Nat.eq_zero_or_pos keys.length with h | h
    · rw [h, zero_mul] at hn
      exact absurd hn.symm (Nat.card_pos (α := C)).ne'
    · exact h
  have hleK : Nat.card K ≤ ∏ i ∈ Finset.range B.length, (T.getD i []).length := by
    rw [hlenK] at hle3
    rw [← hn] at hle3
    exact Nat.le_of_mul_le_mul_left hle3 hpos
  obtain ⟨hcardK, hents, hfac⟩ := chain_prep_le (n := 8330) (w := 14) (by norm_num) (by norm_num)
    (by norm_num) B.length (chainGens G S) (fun i => B.getD i 0) (fun i => R.getD i [])
    (fun i => T.getD i []) (fun i => Ref.getD (i + 1) []) (fun i => Nn.getD i []) hB
    (fun i hi => (hlev i (by omega)).1)
    (fun i hi => by
      have e : chainGens G S (i + 1) = S.getD i [] := by simp [chainGens]
      rw [e]
      exact (hlev i (by omega)).2 hi)
    K h0 hleK
  refine ⟨fun i hi j hj => ⟨(hents i hi j hj).1, (hents i hi j hj).2.1⟩, hfac, ?_⟩
  refine hcomp ?_
  rw [hcardK, hlenK, hn]

end CertificateChecks.KernelHe7222

end
