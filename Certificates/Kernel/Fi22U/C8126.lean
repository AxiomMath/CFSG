
module

public import Certificates.Kernel.Fi22U.UnitaryOrb
public import Certificates.Kernel.Fi22U.UVecB
public import Certificates.Kernel.Sporadic.Fi22.F1Outer
public import CFSG.Certificates.Kernel.Fi22U.CodesSound
public import CFSG.Certificates.Kernel.Fi22U.UnitaryBound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22U.C8126

open CFSG.Monster.B.Fischer CFSG.RankThree.Native.Fi22U CFSG.Fischer CFSG.KC.Fi22U CFSG.KC.Enum
  CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSpor CertificateChecks.KernelFi22U

theorem codeAt_eq {s : String} {cs : List Char} (hs : s = String.ofList cs)
    (hc : ∀ c ∈ cs, c.toNat < 52) {j : Nat} (hj : j < cs.length) :
    codeAt s j = charsC cs / 4 ^ j % 4 := by
  rw [charsC_digit cs hc j hj, codeAt, hs,
    CFSG.KS.Text.get!_toUTF8 (K := cs.length) (fun c h => by
      have := hc c (List.mem_of_mem_take h)
      omega) hj hj]
  have h52 := hc _ (List.getElem_mem hj)
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem B_eq {k : Nat} (hk : k < 693) : fi22UnitaryPoint k = dec (tabC UVec.BN k) := by
  funext i
  rw [fi22UnitaryPoint, dec_apply, co_tabC _ _ i.2, UVec.BN,
    codeAt_eq Fi22OUP.eq (Fi22F1O.codesK_spec Fi22F1O.codesU) (by rw [Fi22F1O.lenU]; omega)]

theorem V_eq {k : Nat} (hk : k < 46) : fi22TransvectionVector k = dec (tabC UVec.VN k) := by
  funext i
  rw [fi22TransvectionVector, dec_apply, co_tabC _ _ i.2, UVec.VN,
    codeAt_eq Fi22OTV.eq (Fi22F1O.codesK_spec Fi22F1O.codesV) (by rw [Fi22F1O.lenV]; omega)]

theorem tab_lt (T k : Nat) : tabC T k < 4096 := Nat.mod_lt _ (by norm_num)

theorem pts : ∀ k < 693, fi22UnitaryPoint k ≠ 0 ∧
    fi22Herm (fi22UnitaryPoint k) (fi22UnitaryPoint k) = 0 ∧
    fi22Normalize (fi22UnitaryPoint k) = fi22UnitaryPoint k := by
  intro k hk
  rw [B_eq hk]
  exact (ptOK_iff (tab_lt _ _)).1 (allN_spec UVec.pts k hk)

theorem lex : ∀ j < 693, ∀ k < 693, j < k →
    fi22LexLt (fi22UnitaryPoint j) (fi22UnitaryPoint k) :=
  fi22LexLt_of_succ fun j hj => by
    rw [B_eq (by omega), B_eq hj]
    exact lex_dec (allN_spec UVec.lex j (by omega))

theorem card : (Finset.univ.filter fun v : Fin 6 → F4 =>
    v ≠ 0 ∧ fi22Herm v v = 0 ∧ fi22Normalize v = v).card = 693 :=
  card_eq_cntPt.trans UVec.cnt

theorem viso : ∀ k < 46,
    fi22Herm (fi22TransvectionVector k) (fi22TransvectionVector k) = 0 := by
  intro k hk
  rw [V_eq hk, herm_dec, beq_iff_eq.1 (allN_spec UVec.viso k hk)]
  rfl

theorem rows : ∀ k < 46, UVec.seedRow k = true := by
  intro k hk
  interval_cases k
  exacts [UVec.seedRow0, UVec.seedRow1, UVec.seedRow2, UVec.seedRow3, UVec.seedRow4,
    UVec.seedRow5, UVec.seedRow6, UVec.seedRow7, UVec.seedRow8, UVec.seedRow9, UVec.seedRow10,
    UVec.seedRow11, UVec.seedRow12, UVec.seedRow13, UVec.seedRow14, UVec.seedRow15,
    UVec.seedRow16, UVec.seedRow17, UVec.seedRow18, UVec.seedRow19, UVec.seedRow20,
    UVec.seedRow21, UVec.seedRow22, UVec.seedRow23, UVec.seedRow24, UVec.seedRow25,
    UVec.seedRow26, UVec.seedRow27, UVec.seedRow28, UVec.seedRow29, UVec.seedRow30,
    UVec.seedRow31, UVec.seedRow32, UVec.seedRow33, UVec.seedRow34, UVec.seedRow35,
    UVec.seedRow36, UVec.seedRow37, UVec.seedRow38, UVec.seedRow39, UVec.seedRow40,
    UVec.seedRow41, UVec.seedRow42, UVec.seedRow43, UVec.seedRow44, UVec.seedRow45]

theorem seeds : ∀ k < 46, ∀ j < 693, fi22UnitaryPoint ((fi22OuterArr693 (15 + k))[j]!) =
    fi22Normalize (fi22Tv (fi22TransvectionVector k) (fi22UnitaryPoint j)) := by
  intro k hk j hj
  have h := allN_spec (rows k hk) j hj
  rw [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
  rw [Fi22F1O.arr693_eq (by omega), Orb.unpack_get hj, B_eq h.1, ← h.2, V_eq hk, B_eq hj,
    tv_dec, norm_dec]

theorem ufacts : Bound.UFacts :=
  ⟨pts, lex, card, Bound.normalize_normalize, fun c v hc => Bound.normalize_smul c v hc, viso,
    seeds⟩

theorem sOK : allN 49 (fun j => Nat.beq (Fi22O693T.L (15 + j)) (Fi22UO.S j)) = true := by
  decide +kernel

theorem bOK : allN 5 (fun t => Nat.beq (#[0, 1, 3, 9, 45][t]!) (pg 10 (mask 10) Fi22UO.BP t)) =
    true := by
  decide +kernel

theorem perms : allN 49 (fun j => permOK 693 10 (mask 10) (693 * 10) (Fi22UO.S j)
    (Fi22UO.SI j)) = true := by
  decide +kernel

theorem binds : Binds 693 10 Fi22UO.S 49 5 Fi22UO.BP (fi22OuterStrong693 2) #[0, 1, 3, 9, 45] := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22OuterStrong693, fi22OuterLines693],
    fun j hj => ?_, rfl, fun t ht => Nat.eq_of_beq_eq_true (allN_spec bOK t ht)⟩
  rw [fi22OuterStrong693_two_get hj, Fi22F1O.arr693_eq (by omega),
    Nat.eq_of_beq_eq_true (allN_spec sOK j hj)]

theorem orbits : rawOrbitSizes 693 (fi22OuterStrong693 2) #[0, 1, 3, 9, 45] =
    [693, 512, 120, 36, 6] := by
  have h := rawOrbitSizesK_orb (NS := 11) (CH := 64) (LR := Fi22UO.LR) (PSI := Fi22UO.SI) binds
    perms Fi22UO.ho (by norm_num)
  have e : (List.range 5).map (fun i => rcnt (Fi22UO.LR i)) = [693, 512, 120, 36, 6] := by
    decide +kernel
  exact h.trans e

theorem chain : rawChainOK 693 ((fi22OuterStrong693 2).extract 0 fi22OuterUnitaryGenCount)
    (fi22OuterStrong693 2) #[0, 1, 3, 9, 45]
    (fi22WordsArr fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations) 4 = true := by
  change rawChainOK 693 ((fi22OuterStrong693 2).extract 0 46) (fi22OuterStrong693 2)
    #[0, 1, 3, 9, 45] (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 46 49
      fi22OuterUnitaryDerivations) 4 = true
  refine rawChainK_of_card_orb 4 binds Fi22UO.head Fi22UO.ho (by norm_num : 693 ≤ 11 * 64) ?_
  rw [orbits]
  exact (Bound.card_closure_le ufacts).trans (by norm_num)

theorem noncomm : eqA 693 (compA 693 (fi22OuterArr693 15) (fi22OuterArr693 16))
    (compA 693 (fi22OuterArr693 16) (fi22OuterArr693 15)) = false := by
  have r15 := rep_fi22OuterPerm693 (L := 15) (by norm_num)
  have r16 := rep_fi22OuterPerm693 (L := 16) (by norm_num)
  refine Bool.eq_false_iff.2 fun he => ?_
  have e := congrArg (fun g : Equiv.Perm (Fin 693) => (g 0 : Nat))
    ((eqA_iff (rep_compA r15 r16) (rep_compA r16 r15)).1 he)
  simp only [Equiv.Perm.mul_apply] at e
  have a0 : (fi22OuterPerm693 16 0 : Nat) = 2 := by
    rw [← r16 0, Fi22F1O.arr693_eq (by norm_num), Orb.unpack_get (by norm_num)]
    decide +kernel
  have a1 : (fi22OuterPerm693 15 0 : Nat) = 0 := by
    rw [← r15 0, Fi22F1O.arr693_eq (by norm_num), Orb.unpack_get (by norm_num)]
    decide +kernel
  have a2 : fi22OuterPerm693 16 0 = 2 := Fin.ext a0
  have a3 : fi22OuterPerm693 15 0 = 0 := Fin.ext a1
  have a4 : (fi22OuterPerm693 15 2 : Nat) = 1 := by
    rw [← r15 2, Fi22F1O.arr693_eq (by norm_num), Orb.unpack_get (by norm_num)]
    decide +kernel
  rw [a2, a3, a2, a4] at e
  exact absurd e (by decide)

theorem facts8126 :
    rawChainOK 693 ((fi22OuterStrong693 2).extract 0 fi22OuterUnitaryGenCount)
      (fi22OuterStrong693 2) #[0, 1, 3, 9, 45]
      (fi22WordsArr fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations) 4 = true ∧
    rawOrbitSizes 693 (fi22OuterStrong693 2) #[0, 1, 3, 9, 45] = [693, 512, 120, 36, 6] ∧
    (∀ k < 693, fi22UnitaryPoint k ≠ 0 ∧
      fi22Herm (fi22UnitaryPoint k) (fi22UnitaryPoint k) = 0 ∧
      fi22Normalize (fi22UnitaryPoint k) = fi22UnitaryPoint k) ∧
    (∀ j < 693, ∀ k < 693, j < k → fi22LexLt (fi22UnitaryPoint j) (fi22UnitaryPoint k)) ∧
    (Finset.univ.filter fun v : Fin 6 → F4 =>
      v ≠ 0 ∧ fi22Herm v v = 0 ∧ fi22Normalize v = v).card = 693 ∧
    (∀ v : Fin 6 → F4, fi22Normalize (fi22Normalize v) = fi22Normalize v) ∧
    (∀ (c : F4) (v : Fin 6 → F4), c ≠ 0 → fi22Normalize (c • v) = fi22Normalize v) ∧
    (∀ k < 46, fi22Herm (fi22TransvectionVector k) (fi22TransvectionVector k) = 0) ∧
    (∀ k < 46, ∀ j < 693, fi22UnitaryPoint ((fi22OuterArr693 (15 + k))[j]!) =
      fi22Normalize (fi22Tv (fi22TransvectionVector k) (fi22UnitaryPoint j))) ∧
    eqA 693 (compA 693 (fi22OuterArr693 15) (fi22OuterArr693 16))
      (compA 693 (fi22OuterArr693 16) (fi22OuterArr693 15)) = false :=
  ⟨chain, orbits, pts, lex, card, Bound.normalize_normalize,
    fun c v hc => Bound.normalize_smul c v hc, viso, seeds, noncomm⟩

end CertificateChecks.KernelFi22U.C8126

end
