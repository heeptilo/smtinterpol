package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The label of a transition in a (non-naive) Dawg.
 * Represents a set of LETTERs together with some (un)equals constraints regarding some COLNAMES.
 * Note that the different constraints are implicitly conjunctive.
 * Disjunctions are expressed via multiple edges.
 * 
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class DawgLetter<LETTER, COLNAMES> {
	
	private final Set<LETTER> mLetters;
	private final Set<COLNAMES> mEqualColnames;
	private final Set<COLNAMES> mUnequalColnames;
	
	final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;

	public DawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf) {
		mDawgLetterFactory = dlf;
		mLetters = null;
		mEqualColnames = null;
		mUnequalColnames = null;
	}
	
	public DawgLetter(Set<LETTER> newLetters, Set<COLNAMES> equalColnames, Set<COLNAMES> inequalColnames,
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory) {
		mDawgLetterFactory = dawgLetterFactory;
		mLetters = Collections.unmodifiableSet(newLetters);
		mEqualColnames = Collections.unmodifiableSet(equalColnames);
		mUnequalColnames = Collections.unmodifiableSet(inequalColnames);
	}

	public Set<DawgLetter<LETTER, COLNAMES>> complement() {

		Set<LETTER> newLetters = new HashSet<LETTER>(mDawgLetterFactory.getAllConstants());
		newLetters.removeAll(mLetters);
		
	
		Set<DawgLetter<LETTER, COLNAMES>> result = new HashSet<DawgLetter<LETTER,COLNAMES>>();
		
		for (COLNAMES cn : mEqualColnames) {
			Set<COLNAMES> es = Collections.emptySet();
			result.add(mDawgLetterFactory.getDawgLetter(
					mDawgLetterFactory.getAllConstants(), es,  Collections.singleton(cn)));
		}
		for (COLNAMES cn : mUnequalColnames) {
			Set<COLNAMES> es = Collections.emptySet();
			result.add(mDawgLetterFactory.getDawgLetter(
					mDawgLetterFactory.getAllConstants(), Collections.singleton(cn), es));
		}	
		return result;
	}

	public DawgLetter<LETTER, COLNAMES> intersect(DawgLetter<LETTER, COLNAMES> other) {
		Set<LETTER> mNewLetters = new HashSet<LETTER>(mLetters);
		Set<COLNAMES> mNewEqualColnames = new HashSet<COLNAMES>(mEqualColnames);
		Set<COLNAMES> mNewUnequalColnames = new HashSet<COLNAMES>(mUnequalColnames);
		
		mNewLetters.retainAll(other.mLetters);
		mNewEqualColnames.addAll(other.mEqualColnames);
		mNewUnequalColnames.addAll(other.mUnequalColnames);
		
		return mDawgLetterFactory.getDawgLetter(mNewLetters, mEqualColnames, mUnequalColnames);
	}

	public boolean matches(LETTER ltr, List<LETTER> word) {
		if (!mLetters.contains(ltr)) {
			return false;
		}
//		if (mEqualColnames.)
		//TODO complete
		
		return false;
	}
}

/**
 * A DawgLetter that captures no LETTER.
 * (probably this should not occur in any Dawg, but only as an intermediate result during construction
 *  -- an edge labelled with this letter should be omitted)
 * 
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
class EmptyDawgLetter<LETTER, COLNAMES> extends DawgLetter<LETTER, COLNAMES> {

	EmptyDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf) {
		super(dlf);
	}

	@Override
	public Set<DawgLetter<LETTER, COLNAMES>> complement() {
		return mDawgLetterFactory.getUniversalDawgLetterSingleton();
	}

	@Override
	public DawgLetter<LETTER, COLNAMES> intersect(DawgLetter<LETTER, COLNAMES> other) {
		return this;
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word) {
		return false;
	}
}

/**
 * A DawgLetter that captures all LETTERs.
 * (i.e. the DawgLetter whose LETTER-set is "allConstants", and whose (un)equals-sets are empty)
 * 
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
class UniversalDawgLetter<LETTER, COLNAMES> extends DawgLetter<LETTER, COLNAMES> {

	UniversalDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf) {
		super(dlf);
	}

	@Override
	public Set<DawgLetter<LETTER, COLNAMES>> complement() {
		return mDawgLetterFactory.getEmptyDawgLetterSingleton();
	}

	@Override
	public DawgLetter<LETTER, COLNAMES> intersect(DawgLetter<LETTER, COLNAMES> other) {
		return other;
	}
	
	@Override
	public boolean matches(LETTER ltr, List<LETTER> word) {
		return true;
	}
}