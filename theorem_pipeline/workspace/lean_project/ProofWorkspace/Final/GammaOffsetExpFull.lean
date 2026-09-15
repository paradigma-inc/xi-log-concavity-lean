import ProofWorkspace.Final.GammaOffsetExpKernelFull
import ProofWorkspace.Final.GammaOffsetChunkAFull
import ProofWorkspace.Final.GammaOffsetChunkBFull
import ProofWorkspace.Final.GammaOffsetChunkCFull

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000000
namespace ReciprocalXi

theorem sourceGammaLogPairs_eq (r : Fin 160) :
    sourceGammaLogPairs.getD r (0,0) =
      (ratLogGammaFastLower (gammaOffsetResidue r) 440 480 400 (10^180),
        ratLogGammaFastUpper (gammaOffsetResidue r) 440 480 400 (10^180)) := by
  fin_cases r
  · exact (show sourceGammaLogPairs.getD 0 (0,0) = gammaOffsetLiteral0 from
      by decide +kernel).trans gammaOffsetLiteral0_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 1 (0,0) = gammaOffsetLiteral1 from
      by decide +kernel).trans gammaOffsetLiteral1_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 2 (0,0) = gammaOffsetLiteral2 from
      by decide +kernel).trans gammaOffsetLiteral2_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 3 (0,0) = gammaOffsetLiteral3 from
      by decide +kernel).trans gammaOffsetLiteral3_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 4 (0,0) = gammaOffsetLiteral4 from
      by decide +kernel).trans gammaOffsetLiteral4_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 5 (0,0) = gammaOffsetLiteral5 from
      by decide +kernel).trans gammaOffsetLiteral5_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 6 (0,0) = gammaOffsetLiteral6 from
      by decide +kernel).trans gammaOffsetLiteral6_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 7 (0,0) = gammaOffsetLiteral7 from
      by decide +kernel).trans gammaOffsetLiteral7_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 8 (0,0) = gammaOffsetLiteral8 from
      by decide +kernel).trans gammaOffsetLiteral8_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 9 (0,0) = gammaOffsetLiteral9 from
      by decide +kernel).trans gammaOffsetLiteral9_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 10 (0,0) = gammaOffsetLiteral10 from
      by decide +kernel).trans gammaOffsetLiteral10_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 11 (0,0) = gammaOffsetLiteral11 from
      by decide +kernel).trans gammaOffsetLiteral11_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 12 (0,0) = gammaOffsetLiteral12 from
      by decide +kernel).trans gammaOffsetLiteral12_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 13 (0,0) = gammaOffsetLiteral13 from
      by decide +kernel).trans gammaOffsetLiteral13_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 14 (0,0) = gammaOffsetLiteral14 from
      by decide +kernel).trans gammaOffsetLiteral14_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 15 (0,0) = gammaOffsetLiteral15 from
      by decide +kernel).trans gammaOffsetLiteral15_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 16 (0,0) = gammaOffsetLiteral16 from
      by decide +kernel).trans gammaOffsetLiteral16_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 17 (0,0) = gammaOffsetLiteral17 from
      by decide +kernel).trans gammaOffsetLiteral17_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 18 (0,0) = gammaOffsetLiteral18 from
      by decide +kernel).trans gammaOffsetLiteral18_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 19 (0,0) = gammaOffsetLiteral19 from
      by decide +kernel).trans gammaOffsetLiteral19_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 20 (0,0) = gammaOffsetLiteral20 from
      by decide +kernel).trans gammaOffsetLiteral20_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 21 (0,0) = gammaOffsetLiteral21 from
      by decide +kernel).trans gammaOffsetLiteral21_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 22 (0,0) = gammaOffsetLiteral22 from
      by decide +kernel).trans gammaOffsetLiteral22_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 23 (0,0) = gammaOffsetLiteral23 from
      by decide +kernel).trans gammaOffsetLiteral23_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 24 (0,0) = gammaOffsetLiteral24 from
      by decide +kernel).trans gammaOffsetLiteral24_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 25 (0,0) = gammaOffsetLiteral25 from
      by decide +kernel).trans gammaOffsetLiteral25_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 26 (0,0) = gammaOffsetLiteral26 from
      by decide +kernel).trans gammaOffsetLiteral26_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 27 (0,0) = gammaOffsetLiteral27 from
      by decide +kernel).trans gammaOffsetLiteral27_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 28 (0,0) = gammaOffsetLiteral28 from
      by decide +kernel).trans gammaOffsetLiteral28_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 29 (0,0) = gammaOffsetLiteral29 from
      by decide +kernel).trans gammaOffsetLiteral29_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 30 (0,0) = gammaOffsetLiteral30 from
      by decide +kernel).trans gammaOffsetLiteral30_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 31 (0,0) = gammaOffsetLiteral31 from
      by decide +kernel).trans gammaOffsetLiteral31_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 32 (0,0) = gammaOffsetLiteral32 from
      by decide +kernel).trans gammaOffsetLiteral32_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 33 (0,0) = gammaOffsetLiteral33 from
      by decide +kernel).trans gammaOffsetLiteral33_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 34 (0,0) = gammaOffsetLiteral34 from
      by decide +kernel).trans gammaOffsetLiteral34_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 35 (0,0) = gammaOffsetLiteral35 from
      by decide +kernel).trans gammaOffsetLiteral35_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 36 (0,0) = gammaOffsetLiteral36 from
      by decide +kernel).trans gammaOffsetLiteral36_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 37 (0,0) = gammaOffsetLiteral37 from
      by decide +kernel).trans gammaOffsetLiteral37_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 38 (0,0) = gammaOffsetLiteral38 from
      by decide +kernel).trans gammaOffsetLiteral38_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 39 (0,0) = gammaOffsetLiteral39 from
      by decide +kernel).trans gammaOffsetLiteral39_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 40 (0,0) = gammaOffsetLiteral40 from
      by decide +kernel).trans gammaOffsetLiteral40_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 41 (0,0) = gammaOffsetLiteral41 from
      by decide +kernel).trans gammaOffsetLiteral41_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 42 (0,0) = gammaOffsetLiteral42 from
      by decide +kernel).trans gammaOffsetLiteral42_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 43 (0,0) = gammaOffsetLiteral43 from
      by decide +kernel).trans gammaOffsetLiteral43_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 44 (0,0) = gammaOffsetLiteral44 from
      by decide +kernel).trans gammaOffsetLiteral44_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 45 (0,0) = gammaOffsetLiteral45 from
      by decide +kernel).trans gammaOffsetLiteral45_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 46 (0,0) = gammaOffsetLiteral46 from
      by decide +kernel).trans gammaOffsetLiteral46_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 47 (0,0) = gammaOffsetLiteral47 from
      by decide +kernel).trans gammaOffsetLiteral47_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 48 (0,0) = gammaOffsetLiteral48 from
      by decide +kernel).trans gammaOffsetLiteral48_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 49 (0,0) = gammaOffsetLiteral49 from
      by decide +kernel).trans gammaOffsetLiteral49_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 50 (0,0) = gammaOffsetLiteral50 from
      by decide +kernel).trans gammaOffsetLiteral50_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 51 (0,0) = gammaOffsetLiteral51 from
      by decide +kernel).trans gammaOffsetLiteral51_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 52 (0,0) = gammaOffsetLiteral52 from
      by decide +kernel).trans gammaOffsetLiteral52_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 53 (0,0) = gammaOffsetLiteral53 from
      by decide +kernel).trans gammaOffsetLiteral53_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 54 (0,0) = gammaOffsetLiteral54 from
      by decide +kernel).trans gammaOffsetLiteral54_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 55 (0,0) = gammaOffsetLiteral55 from
      by decide +kernel).trans gammaOffsetLiteral55_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 56 (0,0) = gammaOffsetLiteral56 from
      by decide +kernel).trans gammaOffsetLiteral56_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 57 (0,0) = gammaOffsetLiteral57 from
      by decide +kernel).trans gammaOffsetLiteral57_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 58 (0,0) = gammaOffsetLiteral58 from
      by decide +kernel).trans gammaOffsetLiteral58_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 59 (0,0) = gammaOffsetLiteral59 from
      by decide +kernel).trans gammaOffsetLiteral59_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 60 (0,0) = gammaOffsetLiteral60 from
      by decide +kernel).trans gammaOffsetLiteral60_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 61 (0,0) = gammaOffsetLiteral61 from
      by decide +kernel).trans gammaOffsetLiteral61_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 62 (0,0) = gammaOffsetLiteral62 from
      by decide +kernel).trans gammaOffsetLiteral62_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 63 (0,0) = gammaOffsetLiteral63 from
      by decide +kernel).trans gammaOffsetLiteral63_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 64 (0,0) = gammaOffsetLiteral64 from
      by decide +kernel).trans gammaOffsetLiteral64_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 65 (0,0) = gammaOffsetLiteral65 from
      by decide +kernel).trans gammaOffsetLiteral65_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 66 (0,0) = gammaOffsetLiteral66 from
      by decide +kernel).trans gammaOffsetLiteral66_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 67 (0,0) = gammaOffsetLiteral67 from
      by decide +kernel).trans gammaOffsetLiteral67_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 68 (0,0) = gammaOffsetLiteral68 from
      by decide +kernel).trans gammaOffsetLiteral68_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 69 (0,0) = gammaOffsetLiteral69 from
      by decide +kernel).trans gammaOffsetLiteral69_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 70 (0,0) = gammaOffsetLiteral70 from
      by decide +kernel).trans gammaOffsetLiteral70_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 71 (0,0) = gammaOffsetLiteral71 from
      by decide +kernel).trans gammaOffsetLiteral71_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 72 (0,0) = gammaOffsetLiteral72 from
      by decide +kernel).trans gammaOffsetLiteral72_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 73 (0,0) = gammaOffsetLiteral73 from
      by decide +kernel).trans gammaOffsetLiteral73_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 74 (0,0) = gammaOffsetLiteral74 from
      by decide +kernel).trans gammaOffsetLiteral74_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 75 (0,0) = gammaOffsetLiteral75 from
      by decide +kernel).trans gammaOffsetLiteral75_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 76 (0,0) = gammaOffsetLiteral76 from
      by decide +kernel).trans gammaOffsetLiteral76_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 77 (0,0) = gammaOffsetLiteral77 from
      by decide +kernel).trans gammaOffsetLiteral77_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 78 (0,0) = gammaOffsetLiteral78 from
      by decide +kernel).trans gammaOffsetLiteral78_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 79 (0,0) = gammaOffsetLiteral79 from
      by decide +kernel).trans gammaOffsetLiteral79_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 80 (0,0) = gammaOffsetLiteral80 from
      by decide +kernel).trans gammaOffsetLiteral80_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 81 (0,0) = gammaOffsetLiteral81 from
      by decide +kernel).trans gammaOffsetLiteral81_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 82 (0,0) = gammaOffsetLiteral82 from
      by decide +kernel).trans gammaOffsetLiteral82_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 83 (0,0) = gammaOffsetLiteral83 from
      by decide +kernel).trans gammaOffsetLiteral83_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 84 (0,0) = gammaOffsetLiteral84 from
      by decide +kernel).trans gammaOffsetLiteral84_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 85 (0,0) = gammaOffsetLiteral85 from
      by decide +kernel).trans gammaOffsetLiteral85_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 86 (0,0) = gammaOffsetLiteral86 from
      by decide +kernel).trans gammaOffsetLiteral86_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 87 (0,0) = gammaOffsetLiteral87 from
      by decide +kernel).trans gammaOffsetLiteral87_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 88 (0,0) = gammaOffsetLiteral88 from
      by decide +kernel).trans gammaOffsetLiteral88_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 89 (0,0) = gammaOffsetLiteral89 from
      by decide +kernel).trans gammaOffsetLiteral89_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 90 (0,0) = gammaOffsetLiteral90 from
      by decide +kernel).trans gammaOffsetLiteral90_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 91 (0,0) = gammaOffsetLiteral91 from
      by decide +kernel).trans gammaOffsetLiteral91_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 92 (0,0) = gammaOffsetLiteral92 from
      by decide +kernel).trans gammaOffsetLiteral92_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 93 (0,0) = gammaOffsetLiteral93 from
      by decide +kernel).trans gammaOffsetLiteral93_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 94 (0,0) = gammaOffsetLiteral94 from
      by decide +kernel).trans gammaOffsetLiteral94_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 95 (0,0) = gammaOffsetLiteral95 from
      by decide +kernel).trans gammaOffsetLiteral95_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 96 (0,0) = gammaOffsetLiteral96 from
      by decide +kernel).trans gammaOffsetLiteral96_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 97 (0,0) = gammaOffsetLiteral97 from
      by decide +kernel).trans gammaOffsetLiteral97_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 98 (0,0) = gammaOffsetLiteral98 from
      by decide +kernel).trans gammaOffsetLiteral98_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 99 (0,0) = gammaOffsetLiteral99 from
      by decide +kernel).trans gammaOffsetLiteral99_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 100 (0,0) = gammaOffsetLiteral100 from
      by decide +kernel).trans gammaOffsetLiteral100_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 101 (0,0) = gammaOffsetLiteral101 from
      by decide +kernel).trans gammaOffsetLiteral101_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 102 (0,0) = gammaOffsetLiteral102 from
      by decide +kernel).trans gammaOffsetLiteral102_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 103 (0,0) = gammaOffsetLiteral103 from
      by decide +kernel).trans gammaOffsetLiteral103_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 104 (0,0) = gammaOffsetLiteral104 from
      by decide +kernel).trans gammaOffsetLiteral104_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 105 (0,0) = gammaOffsetLiteral105 from
      by decide +kernel).trans gammaOffsetLiteral105_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 106 (0,0) = gammaOffsetLiteral106 from
      by decide +kernel).trans gammaOffsetLiteral106_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 107 (0,0) = gammaOffsetLiteral107 from
      by decide +kernel).trans gammaOffsetLiteral107_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 108 (0,0) = gammaOffsetLiteral108 from
      by decide +kernel).trans gammaOffsetLiteral108_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 109 (0,0) = gammaOffsetLiteral109 from
      by decide +kernel).trans gammaOffsetLiteral109_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 110 (0,0) = gammaOffsetLiteral110 from
      by decide +kernel).trans gammaOffsetLiteral110_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 111 (0,0) = gammaOffsetLiteral111 from
      by decide +kernel).trans gammaOffsetLiteral111_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 112 (0,0) = gammaOffsetLiteral112 from
      by decide +kernel).trans gammaOffsetLiteral112_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 113 (0,0) = gammaOffsetLiteral113 from
      by decide +kernel).trans gammaOffsetLiteral113_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 114 (0,0) = gammaOffsetLiteral114 from
      by decide +kernel).trans gammaOffsetLiteral114_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 115 (0,0) = gammaOffsetLiteral115 from
      by decide +kernel).trans gammaOffsetLiteral115_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 116 (0,0) = gammaOffsetLiteral116 from
      by decide +kernel).trans gammaOffsetLiteral116_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 117 (0,0) = gammaOffsetLiteral117 from
      by decide +kernel).trans gammaOffsetLiteral117_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 118 (0,0) = gammaOffsetLiteral118 from
      by decide +kernel).trans gammaOffsetLiteral118_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 119 (0,0) = gammaOffsetLiteral119 from
      by decide +kernel).trans gammaOffsetLiteral119_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 120 (0,0) = gammaOffsetLiteral120 from
      by decide +kernel).trans gammaOffsetLiteral120_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 121 (0,0) = gammaOffsetLiteral121 from
      by decide +kernel).trans gammaOffsetLiteral121_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 122 (0,0) = gammaOffsetLiteral122 from
      by decide +kernel).trans gammaOffsetLiteral122_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 123 (0,0) = gammaOffsetLiteral123 from
      by decide +kernel).trans gammaOffsetLiteral123_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 124 (0,0) = gammaOffsetLiteral124 from
      by decide +kernel).trans gammaOffsetLiteral124_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 125 (0,0) = gammaOffsetLiteral125 from
      by decide +kernel).trans gammaOffsetLiteral125_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 126 (0,0) = gammaOffsetLiteral126 from
      by decide +kernel).trans gammaOffsetLiteral126_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 127 (0,0) = gammaOffsetLiteral127 from
      by decide +kernel).trans gammaOffsetLiteral127_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 128 (0,0) = gammaOffsetLiteral128 from
      by decide +kernel).trans gammaOffsetLiteral128_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 129 (0,0) = gammaOffsetLiteral129 from
      by decide +kernel).trans gammaOffsetLiteral129_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 130 (0,0) = gammaOffsetLiteral130 from
      by decide +kernel).trans gammaOffsetLiteral130_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 131 (0,0) = gammaOffsetLiteral131 from
      by decide +kernel).trans gammaOffsetLiteral131_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 132 (0,0) = gammaOffsetLiteral132 from
      by decide +kernel).trans gammaOffsetLiteral132_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 133 (0,0) = gammaOffsetLiteral133 from
      by decide +kernel).trans gammaOffsetLiteral133_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 134 (0,0) = gammaOffsetLiteral134 from
      by decide +kernel).trans gammaOffsetLiteral134_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 135 (0,0) = gammaOffsetLiteral135 from
      by decide +kernel).trans gammaOffsetLiteral135_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 136 (0,0) = gammaOffsetLiteral136 from
      by decide +kernel).trans gammaOffsetLiteral136_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 137 (0,0) = gammaOffsetLiteral137 from
      by decide +kernel).trans gammaOffsetLiteral137_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 138 (0,0) = gammaOffsetLiteral138 from
      by decide +kernel).trans gammaOffsetLiteral138_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 139 (0,0) = gammaOffsetLiteral139 from
      by decide +kernel).trans gammaOffsetLiteral139_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 140 (0,0) = gammaOffsetLiteral140 from
      by decide +kernel).trans gammaOffsetLiteral140_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 141 (0,0) = gammaOffsetLiteral141 from
      by decide +kernel).trans gammaOffsetLiteral141_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 142 (0,0) = gammaOffsetLiteral142 from
      by decide +kernel).trans gammaOffsetLiteral142_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 143 (0,0) = gammaOffsetLiteral143 from
      by decide +kernel).trans gammaOffsetLiteral143_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 144 (0,0) = gammaOffsetLiteral144 from
      by decide +kernel).trans gammaOffsetLiteral144_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 145 (0,0) = gammaOffsetLiteral145 from
      by decide +kernel).trans gammaOffsetLiteral145_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 146 (0,0) = gammaOffsetLiteral146 from
      by decide +kernel).trans gammaOffsetLiteral146_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 147 (0,0) = gammaOffsetLiteral147 from
      by decide +kernel).trans gammaOffsetLiteral147_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 148 (0,0) = gammaOffsetLiteral148 from
      by decide +kernel).trans gammaOffsetLiteral148_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 149 (0,0) = gammaOffsetLiteral149 from
      by decide +kernel).trans gammaOffsetLiteral149_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 150 (0,0) = gammaOffsetLiteral150 from
      by decide +kernel).trans gammaOffsetLiteral150_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 151 (0,0) = gammaOffsetLiteral151 from
      by decide +kernel).trans gammaOffsetLiteral151_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 152 (0,0) = gammaOffsetLiteral152 from
      by decide +kernel).trans gammaOffsetLiteral152_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 153 (0,0) = gammaOffsetLiteral153 from
      by decide +kernel).trans gammaOffsetLiteral153_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 154 (0,0) = gammaOffsetLiteral154 from
      by decide +kernel).trans gammaOffsetLiteral154_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 155 (0,0) = gammaOffsetLiteral155 from
      by decide +kernel).trans gammaOffsetLiteral155_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 156 (0,0) = gammaOffsetLiteral156 from
      by decide +kernel).trans gammaOffsetLiteral156_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 157 (0,0) = gammaOffsetLiteral157 from
      by decide +kernel).trans gammaOffsetLiteral157_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 158 (0,0) = gammaOffsetLiteral158 from
      by decide +kernel).trans gammaOffsetLiteral158_fast_eq.symm
  · exact (show sourceGammaLogPairs.getD 159 (0,0) = gammaOffsetLiteral159 from
      by decide +kernel).trans gammaOffsetLiteral159_fast_eq.symm

theorem sourceGammaExpPairs_eq_fast (r : Fin 160) :
    sourceGammaExpPairs.getD r (0,0) =
      (ratGammaFastLower (gammaOffsetResidue r) 440 480 400 256 128 (10^180),
        ratGammaFastUpper (gammaOffsetResidue r) 440 480 400 256 128 (10^180)) := by
  rw [←sourceGammaExpPairs_checked r, sourceGammaLogPairs_eq r]
  unfold ratGammaFastLower ratGammaFastUpper
  rw [ratExpScanIntegerLower_eq _ _ _ _ (by norm_num),
    ratExpScanIntegerUpper_eq _ _ _ _ (by norm_num)]

theorem gammaOffsetResidue_bound (r : Fin 160) : |gammaOffsetResidue r| ≤ 1/2 := by
  have hl : (0:ℚ) ≤ (r.val:ℚ) := by positivity
  have hu : (r.val:ℚ) < 160 := by exact_mod_cast r.isLt
  unfold gammaOffsetResidue
  rw [abs_le]
  push_cast
  constructor <;> linarith

theorem sourceGammaExp_actual_enclosure (r : Fin 160) :
    ((sourceGammaExpPairs.getD r (0,0)).1:ℝ) ≤ Real.Gamma (1+(gammaOffsetResidue r:ℝ)) ∧
      Real.Gamma (1+(gammaOffsetResidue r:ℝ)) ≤ ((sourceGammaExpPairs.getD r (0,0)).2:ℝ) := by
  have hlog := sourceGammaLogPairs_exp_applicable r
  rw [sourceGammaLogPairs_eq r] at hlog
  rw [sourceGammaExpPairs_eq_fast r]
  exact ratGammaFast_enclosure (gammaOffsetResidue r) 440 480 400 256 128 (10^180)
    (gammaOffsetResidue_bound r) (by norm_num) (by norm_num) (by norm_num) hlog.1 hlog.2

end ReciprocalXi

