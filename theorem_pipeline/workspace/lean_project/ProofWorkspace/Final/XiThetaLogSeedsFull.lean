import ProofWorkspace.Final.RationalLogBoundsFull

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
noncomputable section
namespace ReciprocalXi

def thetaLogTwoSeed : ℚ := 69314718055994530941723212145817656807550013436025525412068000949339362196969450/(10:ℚ)^80

theorem thetaLogTwoSeed_error :
    |Real.log (2:ℝ)-(thetaLogTwoSeed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (2:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogTwoSeed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

def thetaLogBase0Seed : ℚ := 6062462181643484258060613204042026328620247514472377081451769990871808792215241/(10:ℚ)^80

theorem thetaLogBase0Seed_error :
    |Real.log (17/16:ℝ)-(thetaLogBase0Seed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (17/16:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogBase0Seed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

def thetaLogBase1Seed : ℚ := 17185025692665922234009894605514726493537872385810780205524019843571821418541842/(10:ℚ)^80

theorem thetaLogBase1Seed_error :
    |Real.log (19/16:ℝ)-(thetaLogBase1Seed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (19/16:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogBase1Seed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

def thetaLogBase2Seed : ℚ := 27193371548364175883166949453299916198257474996358962371136444560149966809189937/(10:ℚ)^80

theorem thetaLogBase2Seed_error :
    |Real.log (21/16:ℝ)-(thetaLogBase2Seed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (21/16:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogBase2Seed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

def thetaLogBase3Seed : ℚ := 36290549368936845313782434597748984614037977739941472551591533950941875810601943/(10:ℚ)^80

theorem thetaLogBase3Seed_error :
    |Real.log (23/16:ℝ)-(thetaLogBase3Seed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (23/16:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogBase3Seed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

def thetaLogBase4Seed : ℚ := 44628710262841951153259018061966900674920217109601442734257574497478348753653666/(10:ℚ)^80

theorem thetaLogBase4Seed_error :
    |Real.log (25/16:ℝ)-(thetaLogBase4Seed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (25/16:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogBase4Seed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

def thetaLogBase5Seed : ℚ := 52324814376454783651680722493487084164047113602722733872136296293890839177704803/(10:ℚ)^80

theorem thetaLogBase5Seed_error :
    |Real.log (27/16:ℝ)-(thetaLogBase5Seed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (27/16:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogBase5Seed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

def thetaLogBase6Seed : ℚ := 59470710774669278951434354652920533319251237648172306243895031366920629325907347/(10:ℚ)^80

theorem thetaLogBase6Seed_error :
    |Real.log (29/16:ℝ)-(thetaLogBase6Seed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (29/16:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogBase6Seed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

def thetaLogBase7Seed : ℚ := 66139848224536500826023583870965093814793839303957095527399803450140692871877236/(10:ℚ)^80

theorem thetaLogBase7Seed_error :
    |Real.log (31/16:ℝ)-(thetaLogBase7Seed:ℝ)|≤1/(10:ℝ)^70 := by
  have h := ratLog_enclosure (31/16:ℚ) 80 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  norm_num [thetaLogBase7Seed]
  exact abs_le.mpr ⟨by linarith [h.1,h.2], by linarith [h.1,h.2]⟩

end ReciprocalXi
