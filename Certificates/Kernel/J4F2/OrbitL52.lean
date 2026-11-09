module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Inputs
public import CFSG.Certificates.Kernel.Common.ListWalk

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall
open CFSG.Quasithin.JonesParshall.Curtis
open scoped Matrix

theorem l52_cols :
    ∀ t : Fin 25, ∀ l : Fin 10,
      (fun k => wedgeMat ((trSL' t : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l) =
        decodeV (l52Col.getD (10 * t + l) 0) := by
  decide +kernel

@[expose] def l52ColP : ℕ :=
  188005811440017798032126583794834917495283544014425253129347480454578569879438606735472443960027241100163593560472521343380534969539262265852134538175643675118468887423340705563827000601832011667284744516705152199423764684357024454915810164442734436152111401325063416457761297547329859290534249383207572824100489284352526713423890286872899381269837482265210458964337969797698866291521960934268814850635326046263849403978986976114060515143846816868528442986176081741239366879629567209060202024805306574568205849696740279531825585811670274843126366958449359637790726096646470405893542856871073610259919029071841899747546022462332896908181178794001055681148689372361038759107504557544346937445425114910589270083528719030182034638112882434047666432174458881

@[expose] def l52ColK (i : ℕ) : ℕ := if i < 250 then (l52ColP >>> (10 * i)) &&& 1023 else 0

theorem l52ColK_lt : ∀ i < 250, l52Col.getD i 0 = l52ColK i := by
  decide +kernel

theorem l52Col_getD (i : ℕ) : l52Col.getD i 0 = l52ColK i := by
  by_cases hi : i < 250
  · exact l52ColK_lt i hi
  · have hs : l52Col.size = 250 := by decide
    rw [Array.getD, dif_neg (by omega), l52ColK, if_neg hi]

@[expose] def actK (t c : ℕ) : ℕ :=
  (List.finRange 10).foldl
    (fun acc (l : Fin 10) => if c.testBit l then acc ^^^ l52ColK (10 * t + l) else acc) 0

theorem actC_eq_actK : actC = actK := by
  funext t c
  unfold actC actK
  simp only [l52Col_getD]

@[expose] def certOne (ws : List ℕ) (b : Bool) (c : ℕ) : Bool :=
  c == 0 || (ws.foldr actK (l52BaseC b) == c && ws.all (· < 25))

theorem l52_walk : CFSG.KC.ListWalk.walk certOne l52Words.toList l52Cls.toList 0 = true := by
  decide +kernel

theorem l52_certK :
    ∀ c < 1024, c ≠ 0 →
      (l52Words.getD c []).foldr actK (l52BaseC (l52Cls.getD c false)) = c ∧
        ∀ t ∈ l52Words.getD c [], t < 25 := by
  intro c hc hc0
  have hw : l52Words.size = 1024 := by decide
  have hb : l52Cls.size = 1024 := by decide
  have h := CFSG.KC.ListWalk.walkA_getD certOne [] false l52Words l52Cls l52_walk c
    (by rw [hw]; exact hc) (by rw [hb]; exact hc)
  simpa [certOne, hc0, List.all_eq_true] using h

theorem l52_cert :
    ∀ c < 1024, c ≠ 0 →
      applyC (l52Words.getD c []) (l52BaseC (l52Cls.getD c false)) = c ∧
        ∀ t ∈ l52Words.getD c [], t < 25 := by
  intro c hc hc0
  unfold applyC
  rw [actC_eq_actK]
  exact l52_certK c hc hc0

theorem l52_count_true :
    (Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = true).card = 155 := by
  decide +kernel

theorem l52_count_false :
    (Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = false).card =
      868 := by
  decide +kernel

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall in
open CFSG.Quasithin.JonesParshall.Curtis in
open scoped Matrix in
theorem c7053 :
    (∀ t : Fin 25, ∀ l : Fin 10,
       (fun k => wedgeMat ((trSL' t : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l) =
         decodeV (l52Col.getD (10 * t + l) 0))
    ∧ (∀ c < 1024, c ≠ 0 →
       applyC (l52Words.getD c []) (l52BaseC (l52Cls.getD c false)) = c ∧
         ∀ t ∈ l52Words.getD c [], t < 25)
    ∧ ((Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = true).card = 155)
    ∧ ((Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = false).card =
       868) :=
  ⟨l52_cols, l52_cert, l52_count_true, l52_count_false⟩

end CertificateChecks.KernelJ4F2

end
