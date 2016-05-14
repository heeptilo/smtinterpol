package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprQuantifiedUnitClause;

public class EprHelpers {

	/**
	 * Goes through all the given literals 
	 * and adds all appearing constants to mAppearingConstants
	 */
	public static HashSet<ApplicationTerm> collectAppearingConstants(Literal[] literals, Theory theory) {
		HashSet<ApplicationTerm> result = new HashSet<>();
		for (Literal l : literals) {
			DPLLAtom atom = (DPLLAtom) l.getAtom();
			Term t = atom.getSMTFormula(theory);
			if (!(t instanceof ApplicationTerm))
				continue;
			for (Term p : ((ApplicationTerm) t).getParameters())
				if (p instanceof ApplicationTerm)
					result.add((ApplicationTerm) p);
		}
		return result;
	}	
	
	/**
	 * Apply the substitution sub to Literal l, return the result
	 * @param sub
	 * @param l
	 * @param theory
	 * @return
	 */
//	public static Literal applySubstitution(TTSubstitution sub, Literal l, Theory theory, CClosure cClosure) {
//	public static Literal applySubstitution(TTSubstitution sub, Literal l, Theory theory) {
	public static Literal applySubstitution(TTSubstitution sub, Literal l, EprTheory eprTheory) {
		boolean isPositive = l.getSign() == 1;
		DPLLAtom atom = l.getAtom();
		
		Theory theory = eprTheory.getTheory();

		if (atom instanceof EprQuantifiedPredicateAtom) {
			EprQuantifiedPredicateAtom eqpa = (EprQuantifiedPredicateAtom) atom;
			TermTuple newTT = sub.apply(eqpa.getArgumentsAsTermTuple());
			ApplicationTerm newTerm = theory.term(eqpa.eprPredicate.functionSymbol, newTT.terms);
			EprPredicateAtom result = null;
			if (newTerm.getFreeVars().length > 0) {
				result = eqpa.eprPredicate.getAtomForTermTuple(newTT, theory, l.getAtom().getAssertionStackLevel());
			} else {
				result = eqpa.eprPredicate.getAtomForPoint(newTT, theory, l.getAtom().getAssertionStackLevel());
			}
			return isPositive ? result : result.negate();
		} else if (atom instanceof EprQuantifiedEqualityAtom) {
			EprQuantifiedEqualityAtom eea = (EprQuantifiedEqualityAtom) atom;
			TermTuple newTT = sub.apply(eea.getArgumentsAsTermTuple());
			ApplicationTerm newTerm = theory.term("=", newTT.terms);
			DPLLAtom resultAtom = null;
			if (newTerm.getFreeVars().length > 0) {
				resultAtom = new EprQuantifiedEqualityAtom(newTerm, 0, l.getAtom().getAssertionStackLevel());//TODO: hash
//			} else if (newTerm.getParameters()[0].equals(newTerm.getParameters()[1])) {
			} else {
				// TODO: will need a management for these atoms -- so there are no duplicates..
				//   it's not clear if we want CCEqualities or so, here..
				return new EprGroundEqualityAtom(newTerm, 0, 0);
			}
			
			if (eprTheory.isGroundAllMode()) {
				// we are in the mode where Epr just computes all the groundings of each
				// quantified formula
				// --> thus EprAtoms must become CCEqualities
				Clausifier clausif = eprTheory.getClausifier();
				if (resultAtom instanceof EprGroundPredicateAtom) {
					// basically copied from Clausifier.createBooleanLit()
					SharedTerm st = clausif.getSharedTerm(((EprGroundPredicateAtom) resultAtom).getTerm());

					EqualityProxy eq = clausif.
							createEqualityProxy(st, clausif.getSharedTerm(eprTheory.getTheory().mTrue));
					// Safe since m_Term is neither true nor false
					assert eq != EqualityProxy.getTrueProxy();
					assert eq != EqualityProxy.getFalseProxy();
					resultAtom = eq.getLiteral();	
				} else if (resultAtom instanceof EprGroundEqualityAtom) {
					EqualityProxy eq = new EqualityProxy(clausif, 
							clausif.getSharedTerm(((EprAtom) resultAtom).getArguments()[0]), 
							clausif.getSharedTerm(((EprAtom) resultAtom).getArguments()[1])
							);
					resultAtom = eq.getLiteral();
				} else {
					assert false : "should not happen, right??";
				}
				
			}
			
			return isPositive ? resultAtom : resultAtom.negate();
		} else {
			assert false : "there might be equality replacements";
			return l;
		}
	}

	public static EprQuantifiedUnitClause buildEQLWE(
//			boolean isPositive, 
//			EprQuantifiedPredicateAtom atom, 
			Literal quantifiedPredicateLiteral,
			EprQuantifiedEqualityAtom[] excep,
			EprClause explanation,
			EprTheory eprTheory) {
		assert quantifiedPredicateLiteral.getAtom() instanceof EprQuantifiedPredicateAtom;

		Literal[] lits = new Literal[excep.length + 1];
		for (int i = 0; i < excep.length; i++) {
			lits[i] = excep[i];
		}
//		lits[lits.length - 1] = isPositive ? atom : atom.negate();
		lits[lits.length - 1] = quantifiedPredicateLiteral;

		return new EprQuantifiedUnitClause(lits, eprTheory, explanation);
	}
	
	/**
	 * sub is a unifier for the predicateAtoms in setEqlwe and clauseLit.
	 * Apply sub to the equalities in setEqlwe and eprEqualityAtoms,
	 * return the result as a clause.
	 * @param setEqlwe
	 * @param clauseLit
	 * @param eprEqualityAtoms
	 * @param sub
	 * @return
	 */
	public static Literal[] applyUnifierToEqualities(EprQuantifiedEqualityAtom[] eprEqualityAtoms1,
			EprQuantifiedEqualityAtom[] eprEqualityAtoms2, TTSubstitution sub, EprTheory eprTheory) {
		
		ArrayList<Literal> result = new ArrayList<>();
		for (EprQuantifiedEqualityAtom eea : eprEqualityAtoms1) 
			result.add(EprHelpers.applySubstitution(sub, eea, eprTheory));
		for (EprQuantifiedEqualityAtom eea : eprEqualityAtoms2)
			result.add(EprHelpers.applySubstitution(sub, eea, eprTheory));

		return result.toArray(new Literal[result.size()]);
	}
	
	public static ArrayList<DPLLAtom> substituteInExceptions(
			EprQuantifiedEqualityAtom[] equalities, TTSubstitution sub, EprTheory eprTheory) {
		
		ArrayList<DPLLAtom> result = new ArrayList<>();
		for (EprQuantifiedEqualityAtom eea : equalities) {
			result.add((DPLLAtom) EprHelpers.applySubstitution(sub, eea, eprTheory));
		}
		return result;
	}
	
	public static class Pair<T,U> {
		public final T first;
		public final U second;
		
		public Pair(T f, U s) {
			first = f;
			second = s;
		}
	}
}
