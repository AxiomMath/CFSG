module

public import Certificates.Data.HuppertU38.Data
public import Certificates.Data.Kernel.U38Pts
public meta import Certificates.Data.HuppertU38.Data
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SchreierFam.C188002H
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSchreierFam.U38

@[expose] def d3 : List (List ℤ) := CFSG.RankThree.PartTwo.Sec4.Item434U38.words3.toList.drop 7

end CertificateChecks.KernelSchreierFam.U38

end

#ks_rawchain CertificateChecks.KernelSchreierFam.U38C 513 10 32
  CFSG.RankThree.PartTwo.Sec4.Item434U38.strong3 CFSG.RankThree.PartTwo.Sec4.Item434U38.base3 7
  CertificateChecks.KernelSchreierFam.U38.d3

public section

namespace CertificateChecks.KernelSchreierFam.U38

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Certificates.Kernel.U38 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Prim CFSG.KS.Raw GF64

@[expose] def idx (j : Nat) : Nat := if j < 7 then j else 14 + j

@[expose] noncomputable def PF (k : Nat) : Nat := U38T.F k

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 513 10 (mask 10) (513 * 10) p

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 513 10 (mask 10) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 513 10 (mask 10) p q

@[expose] noncomputable def cjA (g y : Nat) : Nat := pc g (pc y (pinv g))

@[expose] noncomputable def cjI (g y : Nat) : Nat := pc (pinv g) (pc y g)

@[expose] noncomputable def sk (G : Nat) : Bool :=
  siftK 513 10 (mask 10) (513 * 10) (pidn 513 10) U38C.LR U38C.TRI U38C.BP 4 0 G

theorem bS : allN 11 (fun j => Nat.beq (U38C.S j) (PF (idx j))) = true := by quickRfl

theorem perm : allN 11 (fun j => permOK 513 10 (mask 10) (513 * 10) (U38C.S j) (U38C.SI j)) =
    true := by
  quickRfl

theorem bget : ∀ t < 4, base3[t]! = pg 10 (mask 10) U38C.BP t := by decide +kernel

theorem orbs : (List.range 4).map (fun i => rcnt (U38C.LR i)) = [513, 512, 7, 3] := by
  decide +kernel

theorem hNS : 513 ≤ U38C.NS * 32 := by decide +kernel

theorem permF : allN 9 (fun k => bAnd(permOK 513 10 (mask 10) (513 * 10) (PF k) (pinv (PF k)),
    bAnd(cn (PF k), cn (pinv (PF k))))) = true := by
  quickRfl

theorem siftC : allN 2 (fun a => allN 7 fun i =>
    bAnd(sk (cjA (PF (7 + a)) (PF i)), bAnd(sk (cjI (PF (7 + a)) (PF i)),
      bAnd(cn (cjA (PF (7 + a)) (PF i)), cn (cjI (PF (7 + a)) (PF i)))))) = true := by
  quickRfl

@[expose] noncomputable def actK (k j : Nat) : Bool :=
  !(mulVec3 (genMatN k) (ptsVn j) 0 == 0 && mulVec3 (genMatN k) (ptsVn j) 1 == 0 &&
      mulVec3 (genMatN k) (ptsVn j) 2 == 0) &&
    Nat.blt (pg 10 (mask 10) (PF k) j) 513 &&
    Nat.beq (vcode (normV3 (mulVec3 (genMatN k) (ptsVn j) 0) (mulVec3 (genMatN k) (ptsVn j) 1)
      (mulVec3 (genMatN k) (ptsVn j) 2))) (vcode (ptsVn (pg 10 (mask 10) (PF k) j)))

@[expose] def PC : Nat := 46570877842797495664620615328520283229839227941363873905541806845177792705479967821062853819677542699196295528220942948718027381966859637754092374207739672605860561439801365201994067932463075545170326263603021882701283404353900047607840469994242142934772698004651448515229539178453290586452478303139945746700262571196900766541322476244110380406084910036296446545432379932368157908685172228916322896698156156297920682892446880000731243231633561300798927619588763510600889153464929954822422167525707658884751748467588801053386742346883726754325868032016037230535651281503867741916051974150381478589777925872135865246383132029894180820426957236660500151171467657698401285251491780041617890465829055469848764668128532613809866652417071628039103373616775876220383957645975402789600546788039381391014852909634908994111538174413094578578737241830810431734360851347457107811104968975703815658043932139351625900884880104604033004531333029763695093239856952570351983224662797575972391300296136095428118859627543383214473325115687010293786725297766805505087659758111173995395353189594504722207486300401547769251158326551662452021465699726790095457612425659840284245739360409112884778510133440415081240407843224009822510859428353560174348126753856982143495010031440188038649099400116742185112943317122876717245323139104334348166257765252887702813883097234587985494530011194534048655140216712788210059941457158494806970351886866238863498409260756567372325207079518242168052477929426663444021427167114380907674631892332944267139388004484990999777284934141762886757699402500889195008222806781226397056727870608746037550562564945194533027921941442080517516149806075179645648677635168754282824965212294044937668153698216490569258617264195908573914438713463056820004705745917254879639160256848302283497765722234628302918774946372036598384094900920864774266549882513526515612329122222970279410521797982251833564611241893744118209362144296761282997901021500024672996831885331512967807208441838625845240896619568552733930516255511614678304027013388240724503501241131650978596823124715458376958758654817573094820916784490126759644027814475365532605932893851554324371615609616830113075557274522843530659109332223212193747813072967355617039804240016121851319615080096169017467241338088489917329961453745335204643354947766904281297400442323189737641969967059473532265246075796212942455378058341909736259853316115837839091053005655376146629311780496018654269397621995931811333247901168072028656690585204812495470661883853600585389659433335861951580250299630198436615151348590979297387647152603824831460494107712872472631632160867545098854095541787019787740104685980364375418888782630691412206150481795584160755067888962312037746440607656885646791785697602789769923364170759865638132794867793735048172408832

@[expose] def ptsVc (j : Nat) : Fin 3 → GF64 := fun t => ofNat' ((PC >>> (18 * j + 6 * t.val)) &&& 63)

@[expose] def ptsG (n : Nat) : Nat := (PC >>> (6 * n)) &&& 63

theorem ptsL : (ptsArr.toList == (List.range 1539).map ptsG) = true := by decide +kernel

theorem ptsArr_get {n : Nat} (hn : n < 1539) : ptsArr[n]! = ptsG n := by
  have hL : ptsArr.toList = (List.range 1539).map ptsG := beq_iff_eq.1 ptsL
  simp [getElem!_def, ← Array.getElem?_toList, hL, hn]

theorem ptsVn_eq {j : Nat} (hj : j < 513) : ptsVn j = ptsVc j := by
  funext t
  have ht := t.2
  simp only [ptsVn, ptsVc]
  rw [ptsArr_get (by omega), ptsG]
  have e : 6 * (3 * j + t.val) = 18 * j + 6 * t.val := by omega
  rw [e]

@[expose] noncomputable def actF (k j : Nat) : Bool :=
  !(mulVec3 (genMatN k) (ptsVc j) 0 == 0 && mulVec3 (genMatN k) (ptsVc j) 1 == 0 &&
      mulVec3 (genMatN k) (ptsVc j) 2 == 0) &&
    Nat.blt (pg 10 (mask 10) (PF k) j) 513 &&
    Nat.beq (vcode (normV3 (mulVec3 (genMatN k) (ptsVc j) 0) (mulVec3 (genMatN k) (ptsVc j) 1)
      (mulVec3 (genMatN k) (ptsVc j) 2))) (vcode (ptsVc (pg 10 (mask 10) (PF k) j)))

theorem gen_of {k : Nat} (h : (List.range 513).all (actF k) = true) :
    (List.range 513).all (actK k) = true := by
  rw [List.all_eq_true] at h ⊢
  intro j hj
  have hf := h j hj
  have ht : pg 10 (mask 10) (PF k) j < 513 := by
    rw [actF] at hf
    simp only [Bool.and_eq_true] at hf
    exact Nat.le_of_ble_eq_true hf.1.2
  rw [actK, ptsVn_eq (List.mem_range.1 hj), ptsVn_eq ht]
  exact hf

theorem gen0 : (List.range 513).all (actK 0) = true := gen_of (by decide +kernel)

theorem gen1 : (List.range 513).all (actK 1) = true := gen_of (by decide +kernel)

theorem gen2 : (List.range 513).all (actK 2) = true := gen_of (by decide +kernel)

theorem gen3 : (List.range 513).all (actK 3) = true := gen_of (by decide +kernel)

theorem gen4 : (List.range 513).all (actK 4) = true := gen_of (by decide +kernel)

theorem gen5 : (List.range 513).all (actK 5) = true := gen_of (by decide +kernel)

theorem gen6 : (List.range 513).all (actK 6) = true := gen_of (by decide +kernel)

theorem negChain : sk (PF 7) = false ∧ Nat.beq (PF 0) (PF 1) = false := by
  constructor <;> decide +kernel

end CertificateChecks.KernelSchreierFam.U38
