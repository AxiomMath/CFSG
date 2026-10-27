module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1RankCheck

public section

namespace CFSG.KD.Co1RankGen

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

def dagB : List Rows × List Rows × Bool := dag [aR, bR] rankBD

def dagC1 : List Rows × List Rows × Bool := brayRows iotaCRows twoCD1

def dagC2 : List Rows × List Rows × Bool := dag (brayElts dagC1 twoCBray) rankCD2

end CFSG.KD.Co1RankGen

end
