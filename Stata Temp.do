
/*
Generates a two step algorithm that matches individual loans within and across datasets.
This algorithm accounts for missing factors, flexes on information that may be rounded or misreported.

Step 1: Run Matching
Step 2: Finalize dataset of valid matches

*/

cap program drop matchit
program define matchit
	use LoanPurpose state loan_id_llma_mcdash zip5 LTV CLTV FICO purpose ///
		DTI init_rate FRM orig_amt orig Occupancy OriginalTerm default zip3 ///
		hasPMI is_pls Balloon IO NegAm ever_other ever_gse ever_private LoanType if ///
		state == `1' & LoanPurpose == `3' & LoanType == `2' using temp_dedup, clear
	drop state LoanPurpose LoanType
	rename loan_id_llma_mcdash loan_id_llma_mcdash2
	gen running = _n
	tempfile temp_match
	save "`temp_match'", replace

	local z = ceil(_N/2000000) //2 million at a time, maximum
	local gs = ceil(_N/`z')
	di `z'
	count
	di `z'*`gs'
			
	//This gets it to start on the iteration we choose!
	local k = 1
	if `1' == `4' {
		local k = `5'
	}
	forvalues q = `k'/`z' {
		forvalues y = 1/5 {
			di "S`1'_T`2'_P`3' - Cycle `q'/`z', Round `y'"
			use if inrange(running,(`q'-1)*`gs' + 1,`q'*`gs') using "`temp_match'", clear
			drop running
			gen orig_C = orig
			gen orig_amt_C = orig_amt
			
			if `y' == 1 {
				//Do nothing
			}
			else if `y' == 2 {
				replace orig = orig - 1
			}
			else if `y' == 3 {
				replace orig = orig + 1
			}
			else if `y' == 4 {
				replace orig_amt = orig_amt - 1000
			}
			else if `y' == 5 {
				replace orig_amt = orig_amt + 1000
			}
					
			foreach v in zip5 LTV CLTV FICO DTI init_rate FRM Occupancy OriginalTerm default hasPMI purpose is_pls Balloon IO NegAm {
				rename `v' `v'_C
			}
			rename loan_id_llma_mcdash loan_id_llma_mcdash1
			
			count
			joinby orig_amt orig zip3 using "`temp_match'"
			keep if loan_id_llma_mcdash1<loan_id_llma_mcdash2
			duplicates drop loan_id_llma_mcdash1 loan_id_llma_mcdash2, force
			count
			
			drop if abs(init_rate-init_rate_C) > .05 & !missing(init_rate) & !missing(init_rate_C)

			gen matchScore = 0
			gen totalScore = 0

			foreach x in zip5 zip5 LTV LTV FRM orig_amt orig OriginalTerm DTI Occupancy default ///
				FICO init_rate FICO init_rate hasPMI purpose Balloon IO NegAm {
				replace totalScore = totalScore + 1 if !missing(`x') & !missing(`x'_C)
			}

			foreach x in zip5 zip5 FRM orig_amt orig Occupancy default purpose  Balloon IO NegAm {
				replace matchScore = matchScore + 1 if `x' == `x'_C & !missing(`x') & !missing(`x'_C)
			}

			replace matchScore = matchScore + 1 if abs(LTV - LTV_C) < 0.1 & !missing(LTV) & !missing(LTV_C)
			replace matchScore = matchScore + 1 if abs(LTV - LTV_C) < 2 & !missing(LTV) & !missing(LTV_C)
			replace matchScore = matchScore + 1 if abs(DTI-DTI_C) <= 1 & !missing(DTI) & !missing(DTI_C)
			replace matchScore = matchScore + 1 if abs(OriginalTerm-OriginalTerm_C) <= 12 & !missing(OriginalTerm) & !missing(OriginalTerm_C)
			replace matchScore = matchScore + 1 if abs(FICO-FICO_C) < 1 & !missing(FICO) & !missing(FICO_C)
						
			replace totalScore = totalScore - 1 if purpose == 1
			replace matchScore = matchScore - 1 if purpose == 1
					
			gen byte pls_match = 1 if (round(init_rate)==round(init_rate_C) & !missing(init_rate) & !missing(init_rate_C)) & ///
				 ((is_pls == 1 & is_pls_C == 0) | (is_pls == 0 & is_pls_C == 1))
			
			tab pls_match, missing
					
			gen byte zip3_match = (floor(zip5/100)*100 == zip5) + (floor(zip5_C/100)*100 == zip5_C) if floor(zip5/100)==floor(zip5_C/100)
			tab zip3_match
					
			gen dropMe = 0
			replace dropMe = dropMe + 1 if (zip5 != zip5_C & !missing(zip5) & !missing(zip5_C))
			replace dropMe = dropMe + 1 if (FICO != FICO_C & !missing(FICO) & !missing(FICO_C))
			drop if dropMe > 1 & pls_match == . & inlist(zip3_match,.,2,0)
					
			//Trying to capture modified loans
			replace matchScore = matchScore+1 if (OriginalTerm > 367 | OriginalTerm_C > 367) & ///
				abs(OriginalTerm-OriginalTerm_C) > 12 & !missing(OriginalTerm) & !missing(OriginalTerm_C) ///					
				
			//Drops rows that can not be confirmed as true matches.
			drop if totalScore-matchScore > 4
			keep loan_id_llma_mcdash1 loan_id_llma_mcdash2 matchScore totalScore pls_match zip3_match
			count
			if r(N) > 0 {
				duplicates drop 
				tempfile temp`y'_`q'
				save "`temp`y'_`q''", replace
			}
		}
	}
	clear
	forvalues q = 1/`z' {
		forvalues y = 1/5 {
			cap noi append using "`temp`y'_`q''"
			cap noi erase "`temp`y'_`q''"
		}
	}
	compress
	save dedup_S`1'_T`2'_P`3', replace
	erase "`temp_match'"
	di c(current_time)
	end

	
	
cap program drop prepit
program define prepit
	di ""
	di "******************"
	di "Step 2: S`1', T`2', P`3'"
	di "******************"
	di ""
	//Create dataset of valid matches
	use dedup_S`1'_T`2'_P`3', clear
	replace matchScore = matchScore+2 if zip3_match == 1 //Boost zip3-to-zip5 matches
	keep if matchScore == totalScore | (totalScore-matchScore <= 1 & matchScore >= 9) | (totalScore-matchScore <=2 & matchScore >= 11)
	drop if inrange(totalScore-matchScore,1,100) & inrange(zip3_match,1,100) //Only keep perfect matches involving loans with only 3-digit zip codes (GSE loans)
			
	rename (loan_id_llma_mcdash1 loan_id_llma_mcdash2 matchScore totalScore zip3_match) (id_c id_1 ms ts z3m)
	gen priority = 1
	*Keep only valid matches
	global p = 1
	while ($p >= 1) {
		local c1 = _N
		qui	bys id_1 (priority ms): keep if _n == _N
		tempfile temp
		save "`temp'", replace
					
		*Core IDs from any duplicate ID lists
		rename (id_c id_1) (bi_c id_c)
	qui	merge 1:m id_c using "`temp'", keep(1 3) keepusing (id_1) gen(merge1)
		rename (bi_c id_1) (loan_id_llma_mcdash1 loan_id_llma_mcdash2)
	qui	replace loan_id_llma_mcdash2 = 0-_n if loan_id_llma_mcdash2 == .
	qui	merge 1:m loan_id_llma_mcdash1 loan_id_llma_mcdash2 using dedup_S`1'_T`2'_P`3', keep(1 3) gen(merge2)
	
		stack loan_id_llma_mcdash1 id_c ms ts loan_id_llma_mcdash1 loan_id_llma_mcdash2 matchScore totalScore, into(id_c id_1 ms ts) clear
		drop if id_1 == .
		rename _stack priority
		
		if (`c1' == _N) {
			global p = 0
		}
		else {
			local rem = `c1' - _N
			di "Round $p: `rem' removed"
			global p = $p + 1
		}
	}
			
	rename (id_c id_1) (loan_id_core loan_id_llma_mcdash2)
	keep loan_id_core loan_id_llma_mcdash2
							
	save dedup_S`1'_T`2'_P`3'_FS87_step2, replace
	erase "`temp'"
	end


