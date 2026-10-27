
module

public import Certificates.Kernel.Sporadic.Fi24Ext.Decoded
public import CFSG.Sporadic.Fi24.ExtSpecBase
import Certificates.Kernel.Sporadic.Fi24Ext.M0
import Certificates.Kernel.Sporadic.Fi24Ext.M1
import Certificates.Kernel.Sporadic.Fi24Ext.M2
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Fi24.ExtCertBase
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import Certificates.Certificate1016Base

public section

namespace CertificateChecks.KernelFi24Ext

open CFSG.KC.Ord CFSG.KS.Mat3 CFSG.KD.Fi24Ext CFSG.KC.Fi24Ext CFSG.KC.Fi24ExtS
  CFSG.Sporadic.Fi24.Native CFSG.Sporadic.Fi24 CertificateChecks.KernelSpor.Fi24Rels

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24Ext.MX CFSG.KD.BrFi24.MT CFSG.KD.Fi24Fix.MX
  CFSG.KD.Fi24Ext.M3 CFSG.KD.BrFi24.ONE slpMatsN wordW mulW invW rowsOfSeed addW transposeW idW
  ofTrits matF initRows basisRows matT gramInv gramW orthoProj restrictW rootForm rref matA matB

@[expose] def chainReg (z : ℤ) : ℕ :=
  if z = 1 ∨ z = -1 then 0 else if z = 2 then 1 else if z = -2 then 2
  else if 0 < z then z.natAbs else 13 + z.natAbs

@[expose] def genReg (z : ℤ) : ℕ := if 0 < z then 2 + z.natAbs else 15 + z.natAbs

theorem wl_chain : ∀ j < 13, WL j = ((chainWords ())[j]!).map chainReg := by decide +kernel

theorem chain_letters : ∀ j < 13, ∀ z ∈ (chainWords ())[j]!,
    z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by decide +kernel

theorem wl_norm : WL 13 = normWords[0]!.map genReg ∧ WL 14 = normWords[1]!.map genReg := by
  decide +kernel

theorem loc0 : localWords[0]! = (List.replicate 30 (localWords[0]!.take 20)).flatten ∧
    (localWords[0]!.take 20).map genReg = WL 15 := by decide +kernel

theorem loc1 : localWords[1]! = localWords[1]!.take 20 ++
      (List.replicate 4 ((localWords[1]!.drop 20).take 20)).flatten ++ localWords[1]!.drop 100 ∧
    (localWords[1]!.take 20).map genReg = WL 16 ∧
    ((localWords[1]!.drop 20).take 20).map genReg = WL 17 ∧
    (localWords[1]!.drop 100).map genReg = WL 18 := by decide +kernel

#kc_forall_chunks inv_all (fun j => Nat.beq (CFSG.KD.BrFi24.MUL (G j) (Gi j)) CFSG.KD.BrFi24.ONE =
  true) 13 CFSG.KD.Fi24Ext.inv 1

#kc_forall_chunks cm_all (fun i => Nat.beq (CFSG.KD.BrFi24.MUL T (G (Nat.add i 2)))
  (CFSG.KD.BrFi24.MUL (G (Nat.add i 2)) T) = true) 11 CFSG.KD.Fi24Ext.cm 1

theorem prod_eq {X Y Z : ℕ} (hX : Cn X) (hY : Cn Y) (h : Nat.beq (CFSG.KD.BrFi24.MUL X Y) Z = true) :
    Mt Z = Mt X * Mt Y := by
  rw [← Nat.eq_of_beq_eq_true h]; exact (mul_mt hX hY).2

theorem mt_ne_one {X : ℕ} (hX : Cn X) (h : bIf(Nat.beq X CFSG.KD.BrFi24.ONE, false, true) = true) :
    Mt X ≠ 1 := by
  intro e
  rw [← mt_one] at e
  have := mat3_inj (by norm_num) hX cn_one e
  rw [this] at h
  revert h
  rw [show Nat.beq CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.ONE = true from Nat.beq_refl _]
  decide

theorem cn_named {k : ℕ} (hk : k < 94) : Cn (MX k) := cn_MX hk

theorem cnB2 : Cn B2 := cn_named (k := 26) (by norm_num)
theorem cnF : Cn F := cn_named (k := 27) (by norm_num)
theorem cnRr : Cn Rr := cn_named (k := 28) (by norm_num)
theorem cnRF : Cn RF := cn_named (k := 29) (by norm_num)
theorem cnK : Cn K := cn_named (k := 30) (by norm_num)
theorem cnS : Cn S := cn_named (k := 31) (by norm_num)
theorem cnE253 : Cn E253 := cn_named (k := 32) (by norm_num)
theorem cnSRF : Cn SRF := cn_named (k := 33) (by norm_num)
theorem cnE : Cn E := cn_named (k := 34) (by norm_num)
theorem cnT : Cn T := cn_named (k := 35) (by norm_num)
theorem cnP1 : Cn P1 := cn_named (k := 38) (by norm_num)
theorem cnP2 : Cn P2 := cn_named (k := 39) (by norm_num)
theorem cnU : Cn U := cn_named (k := 40) (by norm_num)
theorem cnU2 : Cn U2 := cn_named (k := 41) (by norm_num)
theorem cnU4 : Cn U4 := cn_named (k := 42) (by norm_num)
theorem cnU8 : Cn U8 := cn_named (k := 43) (by norm_num)
theorem cnU16 : Cn U16 := cn_named (k := 44) (by norm_num)
theorem cnH0 : Cn H0 := cn_named (k := 45) (by norm_num)
theorem cnXw : Cn Xw := cn_named (k := 46) (by norm_num)
theorem cnYw : Cn Yw := cn_named (k := 47) (by norm_num)
theorem cnY2 : Cn Y2 := cn_named (k := 48) (by norm_num)
theorem cnY4 : Cn Y4 := cn_named (k := 49) (by norm_num)
theorem cnX2w : Cn X2w := cn_named (k := 50) (by norm_num)
theorem cnH1 : Cn H1 := cn_named (k := 51) (by norm_num)
theorem cnX0 : Cn X0 := cn_named (k := 52) (by norm_num)
theorem cnX1 : Cn X1 := cn_named (k := 53) (by norm_num)
theorem cnQ : Cn Q := cn_named (k := 54) (by norm_num)
theorem cnQi : Cn Qi := cn_named (k := 55) (by norm_num)
theorem cnY0 : Cn Y0 := cn_named (k := 56) (by norm_num)
theorem cnY1 : Cn Y1 := cn_named (k := 57) (by norm_num)

theorem wordW_pw {f : ℤ → Array W} {m : ℤ → Matrix (Fin 781) (Fin 781) (ZMod 3)} :
    ∀ (w : List ℤ) {M0 : Array W} {X0 : Matrix (Fin 781) (Fin 781) (ZMod 3)},
      (∀ z ∈ w, canonRows 781 (f z) = true ∧ matW 781 781 (f z) = m z) →
      canonRows 781 M0 = true → matW 781 781 M0 = X0 →
      canonRows 781 (w.foldl (fun M z => mulW M (f z)) M0) = true ∧
        matW 781 781 (w.foldl (fun M z => mulW M (f z)) M0) = X0 * (w.map m).prod
  | [], _, _, _, h0, h1 => ⟨h0, by rw [List.foldl_nil, h1, List.map_nil, List.prod_nil, Matrix.mul_one]⟩
  | z :: w, M0, X0, h, h0, h1 => by
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← Matrix.mul_assoc]
    obtain ⟨hc, hm⟩ := h z List.mem_cons_self
    refine wordW_pw w (fun z' hz' => h z' (List.mem_cons_of_mem _ hz')) (canonRows_mulW h0 hc) ?_
    rw [pw_mulW (RowsWF.of_canonRows h0) (RowsWF.of_canonRows hc)
      (by rw [(canonRows_spec hc).1]), h1, hm]

theorem wordW_pw' {f : ℤ → Array W} {m : ℤ → Matrix (Fin 781) (Fin 781) (ZMod 3)} (w : List ℤ)
    (h : ∀ z ∈ w, canonRows 781 (f z) = true ∧ matW 781 781 (f z) = m z) :
    canonRows 781 (wordW f w) = true ∧ matW 781 781 (wordW f w) = (w.map m).prod := by
  have := wordW_pw w h canonRows_idW (matW_idW (by norm_num))
  unfold wordW
  rwa [Matrix.one_mul] at this

theorem map_reg_prod {w : List ℤ} {reg : ℤ → ℕ} :
    (w.map fun z => Mt (REG (reg z))) = (w.map reg).map fun r => Mt (REG r) := by
  rw [List.map_map]; rfl

theorem canonRows_matA : canonRows 781 (matA ()) = true := by
  unfold matA; exact canonRows_rowsOfSeed 781 le_rfl _

theorem canonRows_matB : canonRows 781 (matB ()) = true := by
  unfold matB; exact canonRows_rowsOfSeed 781 le_rfl _

theorem B2_mt : Mt B2 = matW 781 781 (mulW (matB ()) (matB ())) := by
  rw [pw_mulW (RowsWF.of_canonRows canonRows_matB) (RowsWF.of_canonRows canonRows_matB)
    (by rw [(canonRows_spec canonRows_matB).1]), ← B_mt, prod_eq cn_B cn_B b2]

theorem getElem!_push_last {α : Type} [Inhabited α] (L : Array α) (x : α) :
    (L.push x)[L.size]! = x := by
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

theorem getElem!_push_of_size {α : Type} [Inhabited α] (L : Array α) (x : α) {i : ℕ}
    (h : L.size = i) : (L.push x)[i]! = x := by
  subst h; exact getElem!_push_last L x

theorem getElem!_mem' {α : Type} [Inhabited α] (L : Array α) (i : ℕ) (h : i < L.size) :
    L[i]! ∈ L := by
  rw [getElem!_pos L i h]; exact Array.getElem_mem _

theorem sg_facts : ∀ j < 13, canonRows 781 (slpMatsN chainWords 13).1[j]! = true ∧
    matW 781 781 (slpMatsN chainWords 13).1[j]! = Mt (G j) ∧
    canonRows 781 (slpMatsN chainWords 13).2[j]! = true ∧
    matW 781 781 (slpMatsN chainWords 13).2[j]! = Mt (Gi j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hget := slpMatsN_get chainWords (j := j) 13 hj
    have hlet : ∀ z ∈ (chainWords ())[j]!,
        canonRows 781 (chainLetterW (slpMatsN chainWords j).1 (slpMatsN chainWords j).2 z) = true ∧
          matW 781 781 (chainLetterW (slpMatsN chainWords j).1 (slpMatsN chainWords j).2 z) =
            Mt (REG (chainReg z)) := by
      intro z hz
      obtain ⟨hz0, hzr⟩ := chain_letters j hj z hz
      by_cases h2 : z.natAbs ≤ 2
      · have : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
        rcases this with rfl | rfl | rfl | rfl
        · rw [chainLetterW_one]
          exact ⟨canonRows_matA, A_mt.symm⟩
        · rw [chainLetterW_neg_one]
          exact ⟨canonRows_matA, A_mt.symm⟩
        · rw [chainLetterW_two]
          exact ⟨canonRows_matB, B_mt.symm⟩
        · rw [chainLetterW_neg_two]
          exact ⟨canonRows_mulW canonRows_matB canonRows_matB, B2_mt.symm⟩
      · have hlt : z.natAbs - 3 < j := by omega
        have hget' := slpMatsN_get chainWords (j := z.natAbs - 3) j hlt
        have hget13 := slpMatsN_get chainWords (j := z.natAbs - 3) 13 (by omega)
        obtain ⟨ihc, ihG, ihci, ihGi⟩ := ih _ hlt (by omega)
        have hne1 : ¬(z = 1 ∨ z = -1) := by omega
        have hne2 : ¬z = 2 := by omega
        have hne3 : ¬z = -2 := by omega
        unfold chainLetterW chainReg
        rw [if_neg hne1, if_neg hne2, if_neg hne3, if_neg hne1, if_neg hne2, if_neg hne3]
        by_cases hpos : 0 < z
        · rw [if_pos hpos, if_pos hpos, getD_eq_getElem!, hget'.1, ← hget13.1]
          have e := reg_G (j := z.natAbs - 3) (by omega)
          rw [show 3 + (z.natAbs - 3) = z.natAbs by omega] at e
          rw [e]
          exact ⟨ihc, ihG⟩
        · rw [if_neg hpos, if_neg hpos, getD_eq_getElem!, hget'.2, ← hget13.2]
          have e := reg_Gi (j := z.natAbs - 3) (by omega)
          rw [show 16 + (z.natAbs - 3) = 13 + z.natAbs by omega] at e
          rw [e]
          exact ⟨ihci, ihGi⟩
    obtain ⟨hwc, hwm⟩ := wordW_pw' _ hlet
    have hG : canonRows 781 (slpMatsN chainWords 13).1[j]! = true ∧
        matW 781 781 (slpMatsN chainWords 13).1[j]! = Mt (G j) := by
      rw [hget.1, slpMatsN_succ]
      refine ⟨hwc, ?_⟩
      rw [hwm, map_reg_prod, ← wl_chain j hj, ← (word_mt (w := j) (by omega)).2, st_G j hj]
    refine ⟨hG.1, hG.2, ?_⟩
    have hGi : (slpMatsN chainWords 13).2[j]! = invW 781 (slpMatsN chainWords 13).1[j]! := by
      rw [hget.2, hget.1, slpMatsN_succ, slpMatsN_succ_snd,
        getElem!_push_of_size _ _ (slpMatsN_size chainWords j).2]
    rw [hGi]
    refine invW781_spec hG.1 ?_
    rw [hG.2, ← prod_eq (cn_G hj) (cn_Gi hj) (inv_all j hj), mt_one]

noncomputable abbrev sgW' : Array (Array W) := (slpMatsN chainWords 13).1

noncomputable abbrev sgiW' : Array (Array W) := (slpMatsN chainWords 13).2

theorem genLetter_ok {z : ℤ} (hz : z ≠ 0 ∧ z.natAbs ≤ 13) :
    canonRows 781 (genLetterW sgW' sgiW' z) = true ∧
      matW 781 781 (genLetterW sgW' sgiW' z) = Mt (REG (genReg z)) := by
  have hlt : z.natAbs - 1 < 13 := by omega
  obtain ⟨hc, hG, hci, hGi⟩ := sg_facts _ hlt
  unfold genLetterW genReg
  by_cases hpos : 0 < z
  · rw [if_pos hpos, if_pos hpos, getD_eq_getElem!]
    have e := reg_G (j := z.natAbs - 1) hlt
    rw [show 3 + (z.natAbs - 1) = 2 + z.natAbs by omega] at e
    rw [e]
    exact ⟨hc, hG⟩
  · rw [if_neg hpos, if_neg hpos, getD_eq_getElem!]
    have e := reg_Gi (j := z.natAbs - 1) hlt
    rw [show 16 + (z.natAbs - 1) = 15 + z.natAbs by omega] at e
    rw [e]
    exact ⟨hci, hGi⟩

theorem word_gen {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 13) :
    canonRows 781 (wordW (genLetterW sgW' sgiW') w) = true ∧
      matW 781 781 (wordW (genLetterW sgW' sgiW') w) =
        ((w.map genReg).map fun r => Mt (REG r)).prod := by
  obtain ⟨h1, h2⟩ := wordW_pw' (m := fun z => Mt (REG (genReg z))) w
    (fun z hz => genLetter_ok (hw z hz))
  exact ⟨h1, by rw [h2, map_reg_prod]⟩

theorem zeroFrom_ofFn_ofTrits {n d m : ℕ} (hd : d ≤ 832) (e : Array ℕ) :
    ZeroFrom d (Array.ofFn (n := n) fun i => ofTrits d fun j => e[m * i.val + j]?.getD 0) := by
  intro i j hj
  by_cases hi : i < n
  · unfold rowW
    rw [Array.getElem?_ofFn]
    simp only [hi, ↓reduceDIte, Option.getD_some]
    rw [ofTrits_val hd, if_neg (by omega)]
  · rw [rowW_ge (by rw [Array.size_ofFn]; omega), W.val_zero]

theorem zeroFrom_matF : ZeroFrom 781 (matF ()) := by
  unfold matF
  exact zeroFrom_ofFn_ofTrits (by norm_num) _

theorem canonRows_matF : canonRows 781 (matF ()) = true :=
  canonRows_of matF_size rowsWF_matF zeroFrom_matF

theorem canonRows_mulW_of {r : ℕ} {X Y : Array W} (hXs : X.size = r) (hX : RowsWF X)
    (hY : RowsWF Y) (hz : ZeroFrom 781 Y) : canonRows r (mulW X Y) = true :=
  canonRows_of (by rw [mulW_size, hXs]) (RowsWF.mulW hX hY) (zeroFrom_mulW hX hY hz)

theorem pw_mul' {X Y : Array W} (hX : RowsWF X) (hY : RowsWF Y) (hYs : Y.size ≤ 781)
    {A B : Matrix (Fin 781) (Fin 781) (ZMod 3)} (hA : matW 781 781 X = A)
    (hB : matW 781 781 Y = B) : matW 781 781 (mulW X Y) = A * B := by
  rw [pw_mulW hX hY hYs, hA, hB]

theorem rowsWF_R : RowsWF (rootForm ()).rows := by
  rw [rootForm_rows]; exact CFSG.KC.Fi24FixS.rowsWF_initRows

theorem R_size : (rootForm ()).rows.size = 253 := by
  rw [rootForm_rows]; exact CFSG.KC.Fi24FixS.initRows_size

theorem R_pw : matW 781 781 (rootForm ()).rows = Mt Rr := by rw [rootForm_rows, Rr_mt]

theorem Rt_pw : matW 781 781 (transposeW 253 781 (rootForm ()).rows) = Mt CFSG.KD.Fi24Fix.R := by
  rw [pw_transposeW rowsWF_R R_size, rootForm_rows, Rt_mt]

theorem zeroFrom_R : ZeroFrom 781 (rootForm ()).rows := by
  rw [rootForm_rows]
  intro i j hj
  by_cases hi : i < 253
  · unfold rowW initRows
    rw [Array.getElem?_ofFn]
    simp only [hi, ↓reduceDIte, Option.getD_some]
    rw [ofTrits_val (by norm_num), if_neg (by omega)]
  · exact zeroFrom_initRows_rows i (by omega) j

noncomputable abbrev KW : Array W := gramW 253 (rootForm ()).rows (matF ())

theorem RF_facts : (mulW (rootForm ()).rows (matF ())).size = 253 ∧
    RowsWF (mulW (rootForm ()).rows (matF ())) ∧ ZeroFrom 781 (mulW (rootForm ()).rows (matF ())) ∧
    matW 781 781 (mulW (rootForm ()).rows (matF ())) = Mt RF := by
  refine ⟨by rw [mulW_size, R_size], RowsWF.mulW rowsWF_R rowsWF_matF,
    zeroFrom_mulW rowsWF_R rowsWF_matF zeroFrom_matF, ?_⟩
  rw [pw_mul' rowsWF_R rowsWF_matF (by rw [matF_size]) R_pw F_mt.symm,
    prod_eq cnRr cnF rf]

theorem K_facts : KW.size = 253 ∧ RowsWF KW ∧ ZeroFrom 253 KW ∧ matW 781 781 KW = Mt K := by
  obtain ⟨h1, h2, -, h4⟩ := RF_facts
  unfold KW gramW
  refine ⟨by rw [mulW_size, h1], RowsWF.mulW h2 (RowsWF.transposeW (by norm_num) _ _),
    zeroFrom_mulW h2 (RowsWF.transposeW (by norm_num) _ _) (zeroFrom_transposeW _), ?_⟩
  rw [pw_mul' h2 (RowsWF.transposeW (by norm_num) _ _) (by rw [transposeW_size]) h4 Rt_pw,
    prod_eq cnRF cn_Rt kk]

theorem S_facts : canonRows 253 (gramInv ()) = true ∧ ZeroFrom 253 (gramInv ()) ∧
    matW 781 781 (gramInv ()) = Mt S := by
  obtain ⟨h1, h2, h3, h4⟩ := K_facts
  unfold gramInv
  refine invW253_spec h1 h2 h3 ?_ ?_ ?_
  · rw [h4, ← prod_eq cnS cnK sk, E253_mt]
  · rw [← E253_mt, ← prod_eq cnE253 cnS es]
  · rw [← E253_mt, ← prod_eq cnS cnE253 se]

theorem orthoProj_facts : RowsWF (orthoProj 253 (rootForm ()).rows (matF ()) (gramInv ())) ∧
    ZeroFrom 781 (orthoProj 253 (rootForm ()).rows (matF ()) (gramInv ())) ∧
    matW 781 781 (orthoProj 253 (rootForm ()).rows (matF ()) (gramInv ())) = Mt E := by
  obtain ⟨r1, r2, r3, r4⟩ := RF_facts
  obtain ⟨s1, s2, s3⟩ := S_facts
  have sw := RowsWF.of_canonRows s1
  have hw : RowsWF (mulW (gramInv ()) (mulW (rootForm ()).rows (matF ()))) := RowsWF.mulW sw r2
  have hm : matW 781 781 (mulW (gramInv ()) (mulW (rootForm ()).rows (matF ()))) = Mt SRF := by
    rw [pw_mul' sw r2 (by rw [r1]; norm_num) s3 r4,
      prod_eq cnS cnRF srf]
  unfold orthoProj
  refine ⟨RowsWF.mulW (RowsWF.transposeW (by norm_num) _ _) hw,
    zeroFrom_mulW (RowsWF.transposeW (by norm_num) _ _) hw (zeroFrom_mulW sw r2 r3), ?_⟩
  rw [pw_mul' (RowsWF.transposeW (by norm_num) _ _) hw
    (by rw [mulW_size, (canonRows_spec s1).1]; norm_num) Rt_pw hm,
    prod_eq cn_Rt cnSRF ee]

theorem T_facts : canonRows 781 (matT ()) = true ∧ matW 781 781 (matT ()) = Mt T := by
  obtain ⟨o1, o2, o3⟩ := orthoProj_facts
  unfold matT
  refine ⟨canonRows_addW (RowsWF.idW (by norm_num)) o1 (zeroFrom_of_canonRows canonRows_idW) o2, ?_⟩
  rw [pw_addW (RowsWF.idW (by norm_num)) o1, matW_idW (by norm_num), o3,
    ← Nat.eq_of_beq_eq_true tt, LO_eq]
  have hadd : Mt (addM3 609961 (2 ^ 609961 - 1) CFSG.KD.BrFi24.ONE E) =
      Mt CFSG.KD.BrFi24.ONE + Mt E := (addM3_sound (d := 781) (by norm_num) cn_one cnE).2
  rw [hadd, mt_one]

theorem baseChecks_true : baseChecks (matT ()) (gramInv ()) = true := by
  obtain ⟨k1, k2, k3, k4⟩ := K_facts
  obtain ⟨s1, s2, s3⟩ := S_facts
  have sw := RowsWF.of_canonRows s1
  unfold baseChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨canonRows_matA, canonRows_matB⟩, T_facts.1⟩, s1⟩, ?_⟩, ?_⟩
  · refine eqRows_of_pw (by norm_num) (canonRows_mulW_of (canonRows_spec s1).1 sw k2
      (k3.mono (by norm_num))) canonRows_idW253 ?_
    rw [pw_mul' sw k2 (by rw [k1]; norm_num) s3 k4, ← prod_eq cnS cnK sk, E253_mt, pw_idW253]
  · refine eqRows_of_pw (by norm_num) (canonRows_mulW_of k1 k2 sw (s2.mono (by norm_num)))
      canonRows_idW253 ?_
    rw [pw_mul' k2 sw (by rw [(canonRows_spec s1).1]; norm_num) k4 s3, ← prod_eq cnK cnS ks,
      E253_mt, pw_idW253]

theorem genChecks_true : genChecks sgW' sgiW' = true := by
  unfold genChecks
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨(slpMatsN_size chainWords 13).1, (slpMatsN_size chainWords 13).2⟩, fun j hj => ?_⟩
  obtain ⟨hc, hG, hci, hGi⟩ := sg_facts j hj
  refine ⟨⟨hc, hci⟩, eqRows_of_pw le_rfl (canonRows_mulW hc hci) canonRows_idW ?_⟩
  rw [pw_mul' (RowsWF.of_canonRows hc) (RowsWF.of_canonRows hci)
    (by rw [(canonRows_spec hci).1]) hG hGi, ← prod_eq (cn_G hj) (cn_Gi hj) (inv_all j hj), mt_one,
    matW_idW (by norm_num)]

theorem norm_size : (normWords.size == 2) = true := by decide +kernel

theorem norm_all : normWords.all (·.all fun z => z != 0 && z.natAbs ≤ 13) = true := by
  rw [← Array.all_toList]; decide +kernel

theorem norm_letters' : ∀ w ∈ normWords.toList, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 13 := by decide +kernel

theorem norm_letters : ∀ w ∈ normWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 13 :=
  fun w hw => norm_letters' w (Array.mem_toList_iff.2 hw)

theorem A_cn : Cn (CFSG.KD.BrFi24.RB 23) := cn_A

theorem normChecks_true : normChecks sgW' sgiW' (matT ()) = true := by
  obtain ⟨t1, t2⟩ := T_facts
  have tw := RowsWF.of_canonRows t1
  have aw := RowsWF.of_canonRows canonRows_matA
  have bw := RowsWF.of_canonRows canonRows_matB
  have ts : (matT ()).size = 781 := (canonRows_spec t1).1
  have as : (matA ()).size = 781 := (canonRows_spec canonRows_matA).1
  have bs : (matB ()).size = 781 := (canonRows_spec canonRows_matB).1
  have cP1 := cnP1
  have cP2 := cnP2
  have cB2 := cnB2
  have hTA : matW 781 781 (mulW (matT ()) (matA ())) = Mt T * Mt (CFSG.KD.BrFi24.RB 23) :=
    pw_mul' tw aw (by rw [as]) t2 A_mt.symm
  have hTB : matW 781 781 (mulW (matT ()) (matB ())) = Mt T * Mt (CFSG.KD.BrFi24.RB 24) :=
    pw_mul' tw bw (by rw [bs]) t2 B_mt.symm
  have hP1 : matW 781 781 (mulW (matT ()) (mulW (mulW (matA ()) (matT ())) (matA ()))) = Mt P1 := by
    rw [pw_mul' tw (RowsWF.mulW (RowsWF.mulW aw tw) aw) (by rw [mulW_size, mulW_size, as]) t2
      (pw_mul' (RowsWF.mulW aw tw) aw (by rw [as]) (pw_mul' aw tw (by rw [ts]) A_mt.symm t2)
        A_mt.symm)]
    have e1 := prod_eq cn_A cnT (Z := CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) T) (Nat.beq_refl _)
    have e2 := (mul_mt (mul_mt cn_A cnT).1 cn_A).2
    have e3 := (mul_mt cnT (mul_mt (mul_mt cn_A cnT).1 cn_A).1).2
    rw [← Nat.eq_of_beq_eq_true p1, e3, e2, e1, Matrix.mul_assoc]
  have hP2 : matW 781 781 (mulW (matT ()) (mulW (mulW (matB ()) (matT ())) (mulW (matB ()) (matB ())))) =
      Mt P2 := by
    rw [pw_mul' tw (RowsWF.mulW (RowsWF.mulW bw tw) (RowsWF.mulW bw bw))
      (by rw [mulW_size, mulW_size, bs]) t2
      (pw_mul' (RowsWF.mulW bw tw) (RowsWF.mulW bw bw) (by rw [mulW_size, bs])
        (pw_mul' bw tw (by rw [ts]) B_mt.symm t2) B2_mt.symm)]
    have e2 := (mul_mt (mul_mt cn_B cnT).1 cB2).2
    have e1 := (mul_mt cn_B cnT).2
    have e3 := (mul_mt cnT (mul_mt (mul_mt cn_B cnT).1 cB2).1).2
    rw [← Nat.eq_of_beq_eq_true p2, e3, e2, e1, Matrix.mul_assoc]
  have cP1w : canonRows 781 (mulW (matT ()) (mulW (mulW (matA ()) (matT ())) (matA ()))) = true :=
    canonRows_mulW t1 (canonRows_mulW (canonRows_mulW canonRows_matA t1) canonRows_matA)
  have cP2w : canonRows 781
      (mulW (matT ()) (mulW (mulW (matB ()) (matT ())) (mulW (matB ()) (matB ())))) = true :=
    canonRows_mulW t1 (canonRows_mulW (canonRows_mulW canonRows_matB t1)
      (canonRows_mulW canonRows_matB canonRows_matB))
  unfold normChecks
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact norm_size
  · exact norm_all
  · obtain ⟨w1, w2⟩ := word_gen (norm_letters _ (getElem!_mem' _ 0 (by decide)))
    refine eqRows_of_pw le_rfl (canonRows_mulW (canonRows_mulW t1 canonRows_matA) t1) w1 ?_
    rw [pw_mul' (RowsWF.mulW tw aw) tw (by rw [ts]) hTA t2, w2, ← wl_norm.1,
      ← (word_mt (w := 13) (by norm_num)).2, st_W0, ← Nat.eq_of_beq_eq_true n0,
      (mul_mt (mul_mt cnT cn_A).1 cnT).2, (mul_mt cnT cn_A).2]
  · obtain ⟨w1, w2⟩ := word_gen (norm_letters _ (getElem!_mem' _ 1 (by decide)))
    refine eqRows_of_pw le_rfl (canonRows_mulW (canonRows_mulW t1 canonRows_matB) t1) w1 ?_
    rw [pw_mul' (RowsWF.mulW tw bw) tw (by rw [ts]) hTB t2, w2, ← wl_norm.2,
      ← (word_mt (w := 14) (by norm_num)).2, st_W1, ← Nat.eq_of_beq_eq_true n1,
      (mul_mt (mul_mt cnT cn_B).1 cnT).2, (mul_mt cnT cn_B).2]
  · intro i hi
    obtain ⟨hc, hG, -, -⟩ := sg_facts (i + 2) (by omega)
    have gw := RowsWF.of_canonRows hc
    have gs := (canonRows_spec hc).1
    refine eqRows_of_pw le_rfl (canonRows_mulW t1 hc) (canonRows_mulW hc t1) ?_
    rw [pw_mul' tw gw (by rw [gs]) t2 hG, pw_mul' gw tw (by rw [ts]) hG t2,
      ← (mul_mt cnT (cn_G (j := i + 2) (by omega))).2,
      ← (mul_mt (cn_G (j := i + 2) (by omega)) cnT).2]
    have := Nat.eq_of_beq_eq_true (cm_all i hi)
    rw [show Nat.add i 2 = i + 2 from rfl] at this
    rw [this]
  · refine eqRows_of_pw le_rfl (canonRows_mulW cP1w cP1w) canonRows_idW ?_
    rw [pw_mul' (RowsWF.of_canonRows cP1w) (RowsWF.of_canonRows cP1w)
      (by rw [(canonRows_spec cP1w).1]) hP1 hP1, ← prod_eq cP1 cP1 p1sq, mt_one,
      matW_idW (by norm_num)]
  · exact eqRows_false_of_pw (by rw [hP1, matW_idW (by norm_num)]; exact mt_ne_one cP1 p1ne)
  · refine eqRows_of_pw le_rfl (canonRows_mulW cP2w (canonRows_mulW cP2w cP2w)) canonRows_idW ?_
    rw [pw_mul' (RowsWF.of_canonRows cP2w) (RowsWF.mulW (RowsWF.of_canonRows cP2w)
      (RowsWF.of_canonRows cP2w)) (by rw [mulW_size, (canonRows_spec cP2w).1]) hP2
      (pw_mul' (RowsWF.of_canonRows cP2w) (RowsWF.of_canonRows cP2w)
        (by rw [(canonRows_spec cP2w).1]) hP2 hP2),
      ← (mul_mt cP2 cP2).2, ← (mul_mt cP2 (mul_mt cP2 cP2).1).2,
      Nat.eq_of_beq_eq_true p2cb, mt_one, matW_idW (by norm_num)]
  · exact eqRows_false_of_pw (by rw [hP2, matW_idW (by norm_num)]; exact mt_ne_one cP2 p2ne)

theorem local_size : (localWords.size == 2) = true := by decide +kernel

theorem local_all : localWords.all (·.all fun z => 3 ≤ z.natAbs && z.natAbs ≤ 13) = true := by
  rw [← Array.all_toList]; decide +kernel

theorem local_letters' : ∀ w ∈ localWords.toList, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 13 := by
  decide +kernel

theorem local_letters : ∀ w ∈ localWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 13 :=
  fun w hw => local_letters' w (Array.mem_toList_iff.2 hw)

theorem H0_pow : Mt H0 = Mt U ^ 30 := by
  have cU := cnU
  have c2 := cnU2
  have c4 := cnU4
  have c8 := cnU8
  have c16 := cnU16
  have e2 := prod_eq cU cU u2
  have e4 := prod_eq c2 c2 u4
  have e8 := prod_eq c4 c4 u8
  have e16 := prod_eq c8 c8 u16
  have h := Nat.eq_of_beq_eq_true h0
  rw [← h, (mul_mt c16 (mul_mt c8 (mul_mt c4 c2).1).1).2, (mul_mt c8 (mul_mt c4 c2).1).2,
    (mul_mt c4 c2).2, e16, e8, e4, e2]
  simp only [← pow_two, ← pow_mul, ← pow_add]
  norm_num

theorem H1_eq : Mt H1 = Mt Xw * (Mt Yw ^ 4 * Mt X2w) := by
  have cY := cnYw
  have c2 := cnY2
  have c4 := cnY4
  have cX := cnXw
  have cX2 := cnX2w
  rw [← Nat.eq_of_beq_eq_true h1, (mul_mt cX (mul_mt c4 cX2).1).2, (mul_mt c4 cX2).2,
    prod_eq c2 c2 y4, prod_eq cY cY y2]
  simp only [← pow_two, ← pow_mul]
  norm_num

theorem H_facts : (canonRows 781 (wordW (genLetterW sgW' sgiW') localWords[0]!) = true ∧
      matW 781 781 (wordW (genLetterW sgW' sgiW') localWords[0]!) = Mt H0) ∧
    (canonRows 781 (wordW (genLetterW sgW' sgiW') localWords[1]!) = true ∧
      matW 781 781 (wordW (genLetterW sgW' sgiW') localWords[1]!) = Mt H1) := by
  have m0 : localWords[0]! ∈ localWords := getElem!_mem' _ 0 (by decide)
  have m1 : localWords[1]! ∈ localWords := getElem!_mem' _ 1 (by decide)
  obtain ⟨a1, a2⟩ := word_gen (local_letters _ m0)
  obtain ⟨b1, b2⟩ := word_gen (local_letters _ m1)
  obtain ⟨u, hu1, hu2⟩ : ∃ u : List ℤ, localWords[0]! = (List.replicate 30 u).flatten ∧
      u.map genReg = WL 15 := ⟨_, loc0⟩
  obtain ⟨x, y, x', hx1, hx2, hx3, hx4⟩ : ∃ x y x' : List ℤ,
      localWords[1]! = x ++ (List.replicate 4 y).flatten ++ x' ∧ x.map genReg = WL 16 ∧
        y.map genReg = WL 17 ∧ x'.map genReg = WL 18 := ⟨_, _, _, loc1⟩
  have eU : Mt U = ((WL 15).map fun r => Mt (REG r)).prod := by
    rw [← st_U]; exact (word_mt (w := 15) (by norm_num)).2
  have eX : Mt Xw = ((WL 16).map fun r => Mt (REG r)).prod := by
    rw [← st_Xw]; exact (word_mt (w := 16) (by norm_num)).2
  have eY : Mt Yw = ((WL 17).map fun r => Mt (REG r)).prod := by
    rw [← st_Yw]; exact (word_mt (w := 17) (by norm_num)).2
  have eX' : Mt X2w = ((WL 18).map fun r => Mt (REG r)).prod := by
    rw [← st_X2w]; exact (word_mt (w := 18) (by norm_num)).2
  refine ⟨⟨a1, ?_⟩, ⟨b1, ?_⟩⟩
  · rw [a2, H0_pow, eU, ← hu2, hu1]
    simp only [List.map_flatten, List.map_replicate, List.prod_flatten, List.prod_replicate]
  · rw [b2, H1_eq, eX, eY, eX', ← hx2, ← hx3, ← hx4, hx1]
    simp only [List.map_append, List.map_flatten, List.map_replicate, List.prod_append,
      List.prod_flatten, List.prod_replicate, Matrix.mul_assoc]

theorem localChecks_true : localChecks sgW' sgiW' (gramInv ()) = true := by
  obtain ⟨r1, r2, r3, r4⟩ := RF_facts
  obtain ⟨s1, s2, s3⟩ := S_facts
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := H_facts
  have sw := RowsWF.of_canonRows s1
  have ss : (gramInv ()).size = 253 := (canonRows_spec s1).1
  have cQ := cnQ
  have cQi := cnQi
  have qc : canonRows 253 (basisRows ()) = true :=
    canonRows_of basisRows_size rowsWF_basisRows (zeroFrom_basisRows.mono (by norm_num))
  have qw := rowsWF_basisRows
  obtain ⟨qi1, qi2, qi3⟩ := invW253_spec basisRows_size qw zeroFrom_basisRows (N := Mt Qi)
    (by rw [← Q_mt, ← prod_eq cQi cQ qiq, E253_mt])
    (by rw [← E253_mt, ← prod_eq cnE253 cQi eqi]) (by rw [← E253_mt, ← prod_eq cQi cnE253 qie])
  have qiw := RowsWF.of_canonRows qi1
  have hSRF : matW 781 781 (mulW (gramInv ()) (mulW (rootForm ()).rows (matF ()))) = Mt SRF := by
    rw [pw_mul' sw r2 (by rw [r1]; norm_num) s3 r4,
      prod_eq cnS cnRF srf]
  have hSRFw := RowsWF.mulW sw r2
  have hSRFs : (mulW (gramInv ()) (mulW (rootForm ()).rows (matF ()))).size = 253 := by
    rw [mulW_size, ss]
  have hX : ∀ {H : Array W} {Hf Xf : ℕ}, canonRows 781 H = true → matW 781 781 H = Mt Hf → Cn Hf →
      Nat.beq (CFSG.KD.BrFi24.MUL SRF (CFSG.KD.BrFi24.MUL Hf CFSG.KD.Fi24Fix.R)) Xf = true →
      canonRows 253 (restrictW (gramInv ()) H) = true ∧ matW 781 781 (restrictW (gramInv ()) H) = Mt Xf := by
    intro H Hf Xf hc hm hcf hck
    have hw := RowsWF.of_canonRows hc
    have hHR : RowsWF (mulW H (transposeW 253 781 (rootForm ()).rows)) :=
      RowsWF.mulW hw (RowsWF.transposeW (by norm_num) _ _)
    unfold restrictW
    refine ⟨canonRows_mulW_of hSRFs hSRFw hHR (zeroFrom_mulW hw (RowsWF.transposeW (by norm_num) _ _)
      ((zeroFrom_transposeW _).mono (by norm_num))), ?_⟩
    rw [pw_mul' hSRFw hHR (by rw [mulW_size, (canonRows_spec hc).1]) hSRF
      (pw_mul' hw (RowsWF.transposeW (by norm_num) _ _) (by rw [transposeW_size]) hm Rt_pw),
      ← Nat.eq_of_beq_eq_true hck, (mul_mt cnSRF (mul_mt hcf cn_Rt).1).2,
      (mul_mt hcf cn_Rt).2]
  obtain ⟨x01, x02⟩ := hX a1 a2 cnH0 x0
  obtain ⟨x11, x12⟩ := hX b1 b2 cnH1 x1
  have hloc : ∀ {X Yr : Array W} {Xf Yf : ℕ}, canonRows 253 X = true → matW 781 781 X = Mt Xf →
      Cn Xf → canonRows 253 Yr = true → matW 781 781 Yr = Mt Yf → Cn Yf →
      Nat.beq (CFSG.KD.BrFi24.MUL Xf Q) (CFSG.KD.BrFi24.MUL Q Yf) = true →
      eqRows 253 (mulW X (basisRows ())) (mulW (basisRows ()) Yr) = true := by
    intro X Yr Xf Yf hc hm hcf yc ym ycf hck
    have xw := RowsWF.of_canonRows hc
    have yw := RowsWF.of_canonRows yc
    refine eqRows_of_pw (by norm_num) (canonRows_mulW_of (canonRows_spec hc).1 xw qw
      ((zeroFrom_basisRows).mono (by norm_num)))
      (canonRows_mulW_of basisRows_size qw yw (zeroFrom_of_canonRows yc)) ?_
    rw [pw_mul' xw qw (by rw [basisRows_size]; norm_num) hm Q_mt.symm,
      pw_mul' qw yw (by rw [(canonRows_spec yc).1]; norm_num) Q_mt.symm ym,
      ← (mul_mt hcf cQ).2, ← (mul_mt cQ ycf).2, Nat.eq_of_beq_eq_true hck]
  unfold localChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨local_size, local_all⟩, qc⟩, qi1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine eqRows_of_pw (by norm_num) (canonRows_mulW_of basisRows_size qw qiw
      (zeroFrom_of_canonRows qi1)) canonRows_idW253 ?_
    rw [pw_mul' qw qiw (by rw [(canonRows_spec qi1).1]; norm_num) Q_mt.symm qi3,
      ← prod_eq cQ cQi qqi, E253_mt, pw_idW253]
  · refine eqRows_of_pw (by norm_num) (canonRows_mulW_of (canonRows_spec qi1).1 qiw qw
      ((zeroFrom_basisRows).mono (by norm_num))) canonRows_idW253 ?_
    rw [pw_mul' qiw qw (by rw [basisRows_size]; norm_num) qi3 Q_mt.symm,
      ← prod_eq cQi cQ qiq, E253_mt, pw_idW253]
  · exact hloc x01 x02 cnX0 (canonRows_rowsOfSeed 253 (by norm_num) _) Y0_mt.symm
      cnY0 l0
  · exact hloc x11 x12 cnX1 (canonRows_rowsOfSeed 253 (by norm_num) _) Y1_mt.symm
      cnY1 l1

theorem extChecks_true : extChecks () = true := by
  unfold extChecks
  change (baseChecks (matT ()) (gramInv ()) && genChecks sgW' sgiW' &&
    normChecks sgW' sgiW' (matT ()) && localChecks sgW' sgiW' (gramInv ())) = true
  rw [baseChecks_true, genChecks_true, normChecks_true, localChecks_true]
  rfl

end CertificateChecks.KernelFi24Ext

end
