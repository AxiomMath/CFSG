
module

public import Certificates.Kernel.WordRelK.TabCheck
public import Certificates.Kernel.WordRelK.LComm
public import Certificates.Kernel.WordRelK.Small
public import Certificates.Kernel.WordRelK.UConjL0
public import Certificates.Kernel.WordRelK.UConjL1
public import Certificates.Kernel.WordRelK.UConjT
public import Certificates.Kernel.WordRelK.UComm
public import CFSG.Certificates.Kernel.WordRelK.Rel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelWordRelK.Rel

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Sp8.WordRel CFSG.KC.WordRelK
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CertificateChecks.KernelWordRelK.Tab

theorem tab_all : ∀ r < 52, tabOK TAB r = true := by
  refine tabOK_of_chunks fun c hc => ?_
  open TabCheck in interval_cases c
  exacts [TabCheck.tab0, TabCheck.tab1, TabCheck.tab2, TabCheck.tab3]

open LComm in
theorem lc_all : ∀ i < 16, lCommRowT TAB i = true := by
  intro i hi
  interval_cases i
  exacts [lc0, lc1, lc2, lc3, lc4, lc5, lc6, lc7, lc8, lc9, lc10, lc11, lc12, lc13, lc14, lc15]

open LComm in
theorem lsq_all : ∀ i < 16, lSqT TAB i = true := by
  intro i hi
  interval_cases i
  exacts [lsq0, lsq1, lsq2, lsq3, lsq4, lsq5, lsq6, lsq7, lsq8, lsq9, lsq10, lsq11, lsq12, lsq13,
    lsq14, lsq15]

open UConjL in
theorem ucl_all : ∀ k < 10, uConjLRowT TAB k = true := by
  intro k hk
  interval_cases k
  exacts [ucl0, ucl1, ucl2, ucl3, ucl4, ucl5, ucl6, ucl7, ucl8, ucl9]

open UConjT in
theorem uct_all : ∀ k < 10, uConjTRowT TAB k = true := by
  intro k hk
  interval_cases k
  exacts [uct0, uct1, uct2, uct3, uct4, uct5, uct6, uct7, uct8, uct9]

open UComm in
theorem ucm_all : ∀ j < 10, uCommRowT TAB j = true := by
  intro j hj
  interval_cases j
  exacts [ucm0, ucm1, ucm2, ucm3, ucm4, ucm5, ucm6, ucm7, ucm8, ucm9]

open Small in
theorem usq_all : ∀ k < 10, uSqT TAB k = true := by
  intro k hk
  interval_cases k
  exacts [usq0, usq1, usq2, usq3, usq4, usq5, usq6, usq7, usq8, usq9]

open Small in
theorem co_all : ∀ i < 9, coDecT TAB i = true := by
  intro i hi
  interval_cases i
  exacts [co0, co1, co2, co3, co4, co5, co6, co7, co8]

open Small in
theorem pa_all : ∀ i < 15, paDecT TAB i = true := by
  intro i hi
  interval_cases i
  exacts [pa0, pa1, pa2, pa3, pa4, pa5, pa6, pa7, pa8, pa9, pa10, pa11, pa12, pa13, pa14]

theorem lComm {i j : Nat} (hi : i < 16) (hj : j < 16) :
    wordX (lWord (2 ^ i) ++ lWord (2 ^ j)) =
      wordX (lWord (2 ^ j) ++ lWord (2 ^ i) ++ tWord ((lCommN.getD i []).getD j 0)) :=
  lComm_wordX tab_all lc_all Small.lCommSym hi hj

theorem lSq {i : Nat} (hi : i < 16) : wordX (lWord (2 ^ i) ++ lWord (2 ^ i)) = 1 :=
  lSq_wordX tab_all lsq_all hi

theorem uConjL {k j : Nat} (hk : k < 10) (hj : j < 16) :
    wordX (uWord k ++ lWord (2 ^ j)) =
      wordX (lWord ((uConjLN.getD k []).getD j (0, 0)).1 ++
        tWord ((uConjLN.getD k []).getD j (0, 0)).2 ++ uWord k) :=
  uConjL_wordX tab_all ucl_all hk hj

theorem uConjT {k j : Nat} (hk : k < 10) (hj : j < 9) :
    wordX (uWord k ++ tWord (2 ^ j)) = wordX (tWord ((uConjTN.getD k []).getD j 0) ++ uWord k) :=
  uConjT_wordX tab_all uct_all hk hj

theorem uSq {k : Nat} (hk : k < 10) :
    wordX (uWord k ++ uWord k) = wordX (lWord (uSqN.getD k (0, 0)).1 ++ tWord (uSqN.getD k (0, 0)).2) :=
  uSq_wordX tab_all usq_all hk

theorem uComm {j k : Nat} (hj : j < 10) (hk : k < 10) :
    wordX (uWord j ++ uWord k) =
      wordX (lWord ((uCommN.getD j []).getD k (0, 0)).1 ++
        tWord ((uCommN.getD j []).getD k (0, 0)).2 ++ uWord k ++ uWord j) :=
  uComm_wordX tab_all ucm_all Small.uCommDiag hj hk

theorem coDec {i : Nat} (hi : i < 9) :
    wordX ((coGens.getD i []).map .lift) =
      wordX (lWord (coDecN.getD i (0, 0)).1 ++ tWord (coDecN.getD i (0, 0)).2) :=
  coDec_wordX tab_all co_all hi

theorem paDec {i : Nat} (hi : i < 15) :
    wordX ((pauliWords.getD i []).map .lift) =
      wordX (lWord (paDecN.getD i (0, 0)).1 ++ tWord (paDecN.getD i (0, 0)).2) :=
  paDec_wordX tab_all pa_all hi

end CertificateChecks.KernelWordRelK.Rel
