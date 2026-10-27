module

public import Certificates.Data.Kernel.PairBnb
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.PairDataE7
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.KC.PairBnb

#kc_each ch129090a i (fun i => bnbR (nbP (packT e7Nb)) (wtF 56 1 1) e7O1 200
  (rootMask 56 119 e7Nb i) 44) 0 63
