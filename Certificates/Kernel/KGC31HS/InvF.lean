module

public import Certificates.Kernel.KGC31HS.Defs
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PinvSSound
import CFSG.Certificates.Kernel.Enum.ZCSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CertificateChecks.KernelHS100

@[expose] noncomputable def exclZ (A B t z : Nat) : Bool :=
  Nat.blt (pg 7 (mask 7) B z) 100 && Nat.blt (pg 7 (mask 7) t z) 100 &&
    Nat.blt (pg 7 (mask 7) B (pg 7 (mask 7) t z)) 100 &&
    !Nat.beq (pg 7 (mask 7) t (pg 7 (mask 7) A (pg 7 (mask 7) t (pg 7 (mask 7) B z))))
      (pg 7 (mask 7) A (pg 7 (mask 7) t (pg 7 (mask 7) B (pg 7 (mask 7) t z))))

@[expose] noncomputable def excl3 (A B t : Nat) : Bool :=
  exclZ A B t 0 || exclZ A B t 1 || exclZ A B t 2

@[expose] noncomputable def porbOneF (m x A B : Nat) (C : List (List Nat)) (t : Nat) : Bool :=
  excl3 A B t || porbOne 100 7 m x C t

@[expose] noncomputable def pactOneF (m x A B t : Nat) : Bool :=
  excl3 A B t || pactOne 100 7 m x t

theorem exclZ_ne {A B t z : Nat} (hz : z < 100) (h : exclZ A B t z = true) :
    Nat.beq (pc 100 7 t (pcj 100 7 A B t)) (pc 100 7 (pcj 100 7 A B t) t) = false := by
  have hn : (100 : Nat) < 2 ^ 32 := by decide
  simp only [exclZ, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases hb : Nat.beq (pc 100 7 t (pcj 100 7 A B t)) (pc 100 7 (pcj 100 7 A B t) t)
  · rfl
  · have e := congrArg (fun p => pg 7 (mask 7) p z) (Nat.eq_of_beq_eq_true hb)
    simp only [pc, pcj, PF.pg_pcomp hn hz, PF.pg_pcomp hn h1, PF.pg_pcomp hn h2,
      PF.pg_pcomp hn h3] at e
    rw [e, Nat.beq_refl] at h4
    exact absurd h4 Bool.false_ne_true

theorem pbadAct_false {m x A B t : Nat} (hm : 1 < m) (hA : ppw 100 7 x 1 = A)
    (hB : ppw 100 7 (pinv 100 7 x) 1 = B) (h : excl3 A B t = true) :
    pbadAct 100 7 m x (pinv 100 7 x) t = false := by
  have hz : ∃ z < 100, exclZ A B t z = true := by
    simp only [excl3, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    exacts [⟨0, by decide, h⟩, ⟨1, by decide, h⟩, ⟨2, by decide, h⟩]
  obtain ⟨z, hz, hZ⟩ := hz
  have h1 := exclZ_ne hz hZ
  unfold pbadAct
  rw [Bool.and_eq_false_iff]
  right
  rw [List.all_eq_false]
  refine ⟨1, List.mem_range.2 hm, ?_⟩
  simp only [hA, hB, h1]
  exact Bool.false_ne_true

theorem porbOne_of_F {m x A B : Nat} {C : List (List Nat)} {t : Nat} (hm : 1 < m)
    (hA : ppw 100 7 x 1 = A) (hB : ppw 100 7 (pinv 100 7 x) 1 = B)
    (h : porbOneF m x A B C t = true) : porbOne 100 7 m x C t = true := by
  unfold porbOneF at h
  cases he : excl3 A B t
  · rw [he, Bool.false_or] at h
    exact h
  · unfold porbOne
    rw [pbadAct_false hm hA hB he]
    rfl

theorem pactOne_of_F {m x A B t : Nat} (hm : 1 < m)
    (hA : ppw 100 7 x 1 = A) (hB : ppw 100 7 (pinv 100 7 x) 1 = B)
    (h : pactOneF m x A B t = true) : pactOne 100 7 m x t = true := by
  unfold pactOneF at h
  cases he : excl3 A B t
  · rw [he, Bool.false_or] at h
    exact h
  · unfold pactOne
    rw [pbadAct_false hm hA hB he]
    rfl

theorem permOK_of_self {t : Nat} (h : permOK 100 7 (mask 7) (100 * 7) t t = true) :
    permOK 100 7 (mask 7) (100 * 7) t (pinv 100 7 t) = true := by
  obtain ⟨h0, -, h2⟩ := CFSG.KC.EnumSound.permOK_sound h
  have hc : CFSG.KS.Prim.canonK 100 7 (mask 7) (100 * 7) t = true := by
    unfold CFSG.KS.Prim.canonK
    simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff, Nat.blt_eq, Nat.beq_eq]
    exact ⟨by decide, h0, fun i hi => (h2 i hi).1⟩
  have hinj : CFSG.KS.PinvS.InjK 100 7 t :=
    ⟨fun i hi => (h2 i hi).1, fun a ha b hb e => by rw [← (h2 a ha).2, ← (h2 b hb).2, e]⟩
  exact CFSG.KS.PinvS.permOK_pinvS hc hinj

@[expose] noncomputable def A2 : Nat := nat_lit 2986656102854619990653697042925518222319033601131962219957236127021416029478936394577902569713323919113643018785300190559440226143014582360990342382189733589033578596699027801081480505255912118493099765280116224
@[expose] noncomputable def B2 : Nat := nat_lit 2146996676586049366156861032951064865937610877276935477226599849464553525197070259808587803929725932667639642156995309805212317852182967121609099134676735798463497995538640830181900403123574160793880391023044224
@[expose] noncomputable def A4 : Nat := nat_lit 206952135133319643399870727714666676167493641612627677402204732600900695525474141935114442028170175738287398752309714419314824066852521790955027645101313708995413782559683688061974027097221050245654833089892099
@[expose] noncomputable def B4 : Nat := nat_lit 468530575369071660886527368968238393568216237180960144729849525741675868332214089425560825844021574814544977287083421414690786508541902260230970967673735046998011987057387628007654988458636135845575177583862483
@[expose] noncomputable def A25 : Nat := nat_lit 94142109811980748104858529831863403901279120246367174409382942446356293162199468069091056705148575006193319706426170833915888873526703480950220000951556912019670749380275190373151533584394891609124992565320370
@[expose] noncomputable def B25 : Nat := nat_lit 1464161692513543109004143444871488966821623222208172799178095282394609119953581075126533668101054109283378803143396527248463872242004902531851706249364910573949727323791880001161032455932730234244385968433454741
@[expose] noncomputable def A7 : Nat := nat_lit 3588413259012443690072508654466858526680066074890364848622466333608724777182365245108823992388531707987476039657947589552907344217593103959870850167240892046365461258725461556217797600718770829534005039194640289
@[expose] noncomputable def B7 : Nat := nat_lit 2531407128890918543821488708973170284932824329691584431151125560221862424226225497078766319624583981770670568439348722643410704563218638113278918665350452332915073241529720464266484705562021309504569809465842913
@[expose] noncomputable def A11 : Nat := nat_lit 3810128591088648455288363274268497140929015305991309368944068674862348492417651519186733277798180515338532266104568698442316732013104198872455432698417002241782227564308653708673432331705688401632072514828108035
@[expose] noncomputable def B11 : Nat := nat_lit 3975485793350610276091422882730813420007729416870671830287492933556037782996620798103915181364804494875583551537081009570722698771684710272764402668794685324220095218430314215770783778198833959534582996943261464

theorem kA2 : Nat.beq (ppw 100 7 (FV.F 2) 1) A2 = true := by quickRfl
theorem kB2 : Nat.beq (ppw 100 7 (pinv 100 7 (FV.F 2)) 1) B2 = true := by quickRfl
theorem kA4 : Nat.beq (ppw 100 7 (FV.F 4) 1) A4 = true := by quickRfl
theorem kB4 : Nat.beq (ppw 100 7 (pinv 100 7 (FV.F 4)) 1) B4 = true := by quickRfl
theorem kA25 : Nat.beq (ppw 100 7 (FV.F 25) 1) A25 = true := by quickRfl
theorem kB25 : Nat.beq (ppw 100 7 (pinv 100 7 (FV.F 25)) 1) B25 = true := by quickRfl
theorem kA7 : Nat.beq (ppw 100 7 X7 1) A7 = true := by quickRfl
theorem kB7 : Nat.beq (ppw 100 7 (pinv 100 7 X7) 1) B7 = true := by quickRfl
theorem kA11 : Nat.beq (ppw 100 7 X11 1) A11 = true := by quickRfl
theorem kB11 : Nat.beq (ppw 100 7 (pinv 100 7 X11) 1) B11 = true := by quickRfl

@[expose] noncomputable def invOneF (j : Nat) : Bool :=
  permOK 100 7 (mask 7) (100 * 7) (RH.E j) (RH.E j) &&
    porbOneF 5 (FV.F 2) A2 B2 C5 (RH.E j) && pactOneF 5 (FV.F 4) A4 B4 (RH.E j) &&
    pactOneF 5 (FV.F 25) A25 B25 (RH.E j) && porbOneF 7 X7 A7 B7 C7 (RH.E j) &&
    pactOneF 11 X11 A11 B11 (RH.E j)

@[expose] noncomputable def invBlkF (k : Nat) : Bool :=
  (List.range' (1000 * k) (min 1000 (RH.N - 1000 * k))).all invOneF

theorem invOne_of_F {j : Nat} (h : invOneF j = true) : invOne j = true := by
  simp only [invOneF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [invOne, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨permOK_of_self h1, porbOne_of_F (by decide) (Nat.eq_of_beq_eq_true kA2) (Nat.eq_of_beq_eq_true kB2) h2⟩,
    pactOne_of_F (by decide) (Nat.eq_of_beq_eq_true kA4) (Nat.eq_of_beq_eq_true kB4) h3⟩,
    pactOne_of_F (by decide) (Nat.eq_of_beq_eq_true kA25) (Nat.eq_of_beq_eq_true kB25) h4⟩,
    porbOne_of_F (by decide) (Nat.eq_of_beq_eq_true kA7) (Nat.eq_of_beq_eq_true kB7) h5⟩,
    pactOne_of_F (by decide) (Nat.eq_of_beq_eq_true kA11) (Nat.eq_of_beq_eq_true kB11) h6⟩

end CertificateChecks.KernelKGC31HS

end
