module

public import Certificates.Kernel.PresLetters.F6145
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

namespace CertificateChecks.ONanCM

open CFSG.OddStandard.ONanRec.CM CFSG.CosetTable CFSG.Certificates CFSG.KC.MiscCoset

theorem card_step {m : ℕ} (ws : List (List (Fin m × Bool))) (hm : m < 256) (T : List (Fin m))
    {n N : ℕ} (hi : KB.TableFact m (ws.map encW) (T.map fun x => [(x.val, true)]) n)
    (hr : Finite (PG T.length (restrictWords T ws)) ∧
      Nat.card (PG T.length (restrictWords T ws)) ≤ N) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * N :=
  card_le_of_index_restrict ws T (TableFact.genSub_index ws hm T hi) hr

theorem cmRelWords_card_le : Finite (PG 6 cmRelWords) ∧ Nat.card (PG 6 cmRelWords) ≤ 161280 :=
  card_step cmRelWords (by decide) (subsetOf 6 [0, 1, 2, 3, 4]) CFSG.KBFact.PL6145a
    (card_step cmChain1 (by decide) (subsetOf _ [0, 1, 2, 4]) CFSG.KBFact.PL6145b
      (card_step cmChain2 (by decide) (subsetOf _ [0, 1, 2]) CFSG.KBFact.PL6145c
        (card_step cmChain3 (by decide) (subsetOf _ [0, 1]) CFSG.KBFact.PL6145d
          (card_step cmChain4 (by decide) (subsetOf _ [0]) CFSG.KBFact.PL6145e
            (TableFact.card cmChain5 (by decide) CFSG.KBFact.PL6145f)))))

end CertificateChecks.ONanCM
