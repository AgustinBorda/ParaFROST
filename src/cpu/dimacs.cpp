/***********************************************************************[dimacs.cpp]
Copyright(c) 2020, Muhammad Osama - Anton Wijs,
Technische Universiteit Eindhoven (TU/e).

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
**********************************************************************************/

#include "solve.h"
#include "dimacs.h"
#include "control.h"

using namespace ParaFROST;

bool Solver::parser() 
{
	FAULT_DETECTOR;
	iadd();
	Lits_t c, org;
	org.push(V2DEC(1,0));
	if(!itoClause(c,org)) return false;
	return true;
}

bool Solver::toClause(Lits_t& c, Lits_t& org, char*& str)
{
	assert(c.empty());
	assert(org.empty());
	uint32 v = 0, s = 0;
	bool satisfied = false;
	while ((v = toInteger(str, s)) != 0) {
		if (v > inf.maxVar) PFLOGE("too many variables");
		uint32 lit = V2DEC(v, s);
		CHECKLIT(lit);
		org.push(lit);
		// checking literal
		LIT_ST marker = l2marker(lit);
		if (UNASSIGNED(marker)) {
			markLit(lit);
			LIT_ST val = sp->value[lit];
			if (UNASSIGNED(val)) c.push(lit);
			else if (val) satisfied = true;
		}
		else if (marker != SIGN(lit)) satisfied = true; // tautology
	}
	forall_clause(org, k) {
		unmarkLit(*k);
	}
	if (satisfied) {
		if (opts.proof_en) proof.deleteClause(org);
	}
	else {
		int newsize = c.size();
		if (!newsize) {
			if (opts.proof_en) proof.addEmpty();
			return false; 
		}
		else if (newsize == 1) {
			const uint32 unit = *c;
			CHECKLIT(unit);
			LIT_ST val = sp->value[unit];
			if (UNASSIGNED(val)) enqueueUnit(unit), formula.units++;
			else if (!val) return false;
		}
		else if (orgs.size() + 1 > inf.nOrgCls) PFLOGE("too many clauses");
		else if (newsize) {
			if (newsize == 2) formula.binaries++;
			else if (newsize == 3) formula.ternaries++;
			else assert(newsize > 3), formula.large++;
			if (newsize > formula.maxClauseSize)
				formula.maxClauseSize = newsize;
			newClause(c, false);
		}
		if (opts.proof_en && newsize < org.size()) {
			proof.addClause(c);
			proof.deleteClause(org);
			org.clear();
		}
	}
	c.clear(), org.clear();
	return true;
}

bool Solver::toClause(Lits_t& c, Lits_t& org, int& ch)
{
	assert(c.empty());
	assert(org.empty());
	uint32 v = 0, s = 0;
	bool satisfied = false;
	while ((v = formula.toInteger(ch, s)) != 0) {
		formula.eatWS(ch);
		if (v > inf.maxVar) PFLOGE("too many variables");
		uint32 lit = V2DEC(v, s);
		CHECKLIT(lit);
		org.push(lit);
		// checking literal
		LIT_ST marker = l2marker(lit);
		if (UNASSIGNED(marker)) {
			markLit(lit);
			LIT_ST val = sp->value[lit];
			if (UNASSIGNED(val)) c.push(lit);
			else if (val) satisfied = true;
		}
		else if (marker != SIGN(lit)) satisfied = true; // tautology
	}
	forall_clause(org, k) {
		unmarkLit(*k);
	}
	if (satisfied) {
		if (opts.proof_en) proof.deleteClause(org);
	}
	else {
		int newsize = c.size();
		if (!newsize) {
			if (opts.proof_en) proof.addEmpty();
			PFLOG2(1, "  Found empty clause");
			return false;
		}
		else if (newsize == 1) {
			const uint32 unit = *c;
			CHECKLIT(unit);
			LIT_ST val = sp->value[unit];
			if (UNASSIGNED(val)) enqueueUnit(unit), formula.units++;
			else if (!val) return false;
		}
		else if (orgs.size() + 1 > inf.nOrgCls) PFLOGE("too many clauses");
		else if (newsize) {
			if (newsize == 2) formula.binaries++;
			else if (newsize == 3) formula.ternaries++;
			else assert(newsize > 3), formula.large++;
			if (newsize > formula.maxClauseSize)
				formula.maxClauseSize = newsize;
			newClause(c, false);
		}
		if (opts.proof_en && newsize < org.size()) {
			proof.addClause(c);
			proof.deleteClause(org);
			org.clear();
		}
	}
	c.clear(), org.clear();
	return true;
}
