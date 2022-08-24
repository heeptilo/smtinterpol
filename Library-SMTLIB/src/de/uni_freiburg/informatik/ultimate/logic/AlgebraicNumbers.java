/*
 * Copyright (C) Tilo Heep
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */

package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

//import java.util.*;

/**
 * Class representing the Algebraic Numbers. Every algebraic number is represented
 * by a polynomial and an interval to make it unique.
 * The class is provided with the following functions:
 * squareFree, addition, multiplication, substraction, division and minimize
 */
public class AlgebraicNumbers {

    Polynomial polynomial;
    Rational [] interval = new Rational[2];
    List<Polynomial> sturmSequence;
    List<Polynomial> polynomialFactors = new ArrayList<>();

    public AlgebraicNumbers(Polynomial p, Rational intervallow, Rational intervalhigh) {
        polynomial = p;
        interval[0] = intervallow;
        interval[1] = intervalhigh;
        if (p.getSize() == 0) {
            sturmSequence = new ArrayList<>();
        } else {
            BuildSturmSequence();
        }
    }

    public AlgebraicNumbers(Polynomial p, Integer numberOfRoot) {
        AlgebraicNumbers a = new AlgebraicNumbers(
            p, Rational.valueOf(1, 1), Rational.valueOf(2, 1));
        a = a.squareFree();
        if (a.rootsOfPoly() == 0) {
            //TODO: Error
        } else {
            System.out.println(numberOfRoot);
            a.findRoot(numberOfRoot);
            if (interval[0] == Rational.ZERO && interval[1] == Rational.ZERO) {
                a = AlgebraicNumbers.ZERO;
            }
        }
        polynomial = a.polynomial;
        interval = a.interval;
        sturmSequence = a.sturmSequence;
    }

    /**
     * given a rootID this function finds on polynomial p the root
     * with number rootID beginning with one from the left
     * @param rootID
     */
    private void findRoot(Integer rootID) {
        Rational [] sturmSequenceZero = evaluateSturmsequence(Rational.ZERO);
        Integer rootsSmallerEqZero = SignChangeCounter(SturmsequenceMinusInf()) - SignChangeCounter(sturmSequenceZero);
        Integer rootsGreaterZero = SignChangeCounter(sturmSequenceZero) - SignChangeCounter(SturmsequenceInf());
        Integer end = 2;
        // maxRoots is the number of roots one can possible reach
        // (in either positive or negative direction)
        Integer maxRoots = rootsGreaterZero;
        if (rootID <= rootsSmallerEqZero) {
           // search negative
           end = -2;
           maxRoots = rootsSmallerEqZero;
        }
        // roots in the interval between 0 and end (sign doesnt matter)
        Integer numRoots = rootsInterval(0, end);
        while (numRoots < maxRoots) {
            end *= 2;
            numRoots = rootsInterval(0, end);
            System.out.println(numRoots);
        }
        Rational up = Rational.ZERO;
        Rational down = Rational.valueOf(end, 1);
        Integer numRootsUp;
        Integer numRootsDown;
        while (numRoots > 1) {
            // mid = (up + down) / 2
            Rational mid = up.add(down).div(Rational.valueOf(2, 1));
            numRootsUp = rootsInterval(mid, up);
            numRootsDown = rootsInterval(down, mid);
            if (numRootsDown >= rootID) {
                up = mid;
            } else {
                down = mid;
            }
            // update numRoots
            numRoots = rootsInterval(down, up);
        }
        // choose the smaller one as the lower bound
        if (down.sub(up).isNegative()) {
            interval[0] = down;
            interval[1] = up;
        } else {
            interval[1] = down;
            interval[0] = up;
        }
        return;
    }

    public String toString() {
        if (isZero()) {
            String result = "Zero";
            return result;
        }
        String result = "";
        for (int i = 1; i <= polynomial.coefficients.length; i++) {
            Rational coef = polynomial.coefficients[polynomial.coefficients.length - i];
            if (coef == Rational.ZERO) {
                continue;
            }
            if (i != 1 && !coef.isNegative()) {
                result += "+";
            }
            result += coef;
            if (polynomial.coefficients.length - i > 0) {
                result += "x**" + (polynomial.coefficients.length - i);
            }
        }
        result += " (" + interval[0] + ":" + interval[1] + "]";
        result += " (" + numberOfRoot() + "/" + rootsOfPoly() + ")";
        if (rootsInInterval() > 1) {
            result += " not unique!";
        }
        return result;
    }

    private Integer rootsInterval(Integer intervalstart, Integer intervalend) {
        Integer intervallow = intervalstart;
        Integer intervalhigh = intervalend;
        // if intervalend smaller than intervalstart switch
        if (intervalend < intervalstart) {
            intervallow = intervalend;
            intervalhigh = intervalstart;
        }
        return SignChangeCounter(
            evaluateSturmsequence(Rational.valueOf(intervallow, 1))) -
             SignChangeCounter(evaluateSturmsequence(Rational.valueOf(intervalhigh, 1)));
    }

    private Integer rootsInterval(Rational intervalstart, Rational intervalend) {
        Rational intervallow = intervalstart;
        Rational intervalhigh = intervalend;
        // if intervalend smaller than intervalstart switch
        if (intervalend.sub(intervalstart).isNegative()) {
            intervallow = intervalend;
            intervalhigh = intervalstart;
        }
        return SignChangeCounter(
            evaluateSturmsequence(intervallow)) -
             SignChangeCounter(evaluateSturmsequence(intervalhigh));
    }

    private AlgebraicNumbers improveInterval() {
        Rational midInterval = interval[0].add(interval[1]).div(Rational.valueOf(2, 1));
        AlgebraicNumbers a = new AlgebraicNumbers(polynomial, interval[0], midInterval);
        if (a.rootsInInterval() == 1) {
            return a;
        } else {
            return new AlgebraicNumbers(polynomial, midInterval, interval[1]);
        }
    }
    
    private AlgebraicNumbers inverse() {
        if (isZero()) {
            return this;
        }
        // calculate new interval wrt. the < relation
        Rational idown;
        Rational iup;
        idown = interval[1].inverse();
        iup = interval[0].inverse();
        // if lower number is negative and higher isnt the relation is preserved
        if (interval[0].isNegative() && !interval[1].isNegative()) {
            idown = interval[0].inverse();
            iup = interval[1].inverse();
        }
        if (interval[0] == Rational.ZERO) {
            iup = Rational.ZERO;
        }
        if (interval[1] == Rational.ZERO) {
            idown = Rational.ZERO;
        }
        AlgebraicNumbers inv = new AlgebraicNumbers(polynomial.reverse().removeZeros(), idown, iup);
        return inv;
    }

    public AlgebraicNumbers negate() {
        System.out.println(this);
        if (isZero()) {
            return this;
        }
        // calculate new interval wrt. the < relation
        Rational idown;
        Rational iup;
        idown = interval[1].negate();
        iup = interval[0].negate();
        AlgebraicNumbers neg = new AlgebraicNumbers(polynomial.negate(), idown, iup);
        System.out.println(neg);
        System.out.println(neg.numberOfRoot());
        System.out.println(neg.rootsInInterval());
        // number of roots in interval can be zero if upper bound was root
        // because lower bound is not included in contrast to upper bound
        Rational multi = Rational.valueOf(1, 1);
        while (neg.rootsInInterval() != 1) {
            idown = idown.sub(multi);
            multi.mul(Rational.valueOf(1, 2));
            neg = new AlgebraicNumbers(polynomial.negate(), idown, iup);
        }
        return neg;
    }

    /**
     * Function squareFree takes no arguments and manipulates the polynomial such
     * that it represents the same roots but every root just once. 
     */
    private AlgebraicNumbers squareFree() {
        if (isZero()) {
            return this;
        }
        Polynomial result = new Polynomial();
        Polynomial diff = new Polynomial();
        Polynomial gcd = new Polynomial();
        diff = polynomial.differentiate();
        gcd = ManPolys.gcd(polynomial, diff);
        if (gcd.coefficients.length <= 1) {
            // größter gemeinsamer teiler konstant
            return this;
        }
        result = ManPolys.longdivision(polynomial, gcd)[0];
        return new AlgebraicNumbers(result, interval[0], interval[1]);
    }

    private void BuildSturmSequence() {
        List<Polynomial> res1 = new ArrayList<>();
        int i = polynomial.getDegree();
        if (i <= 0) {
            return;
        }
        Polynomial diffPoly1 = polynomial.copy();
        Polynomial diffPoly2 = polynomial.differentiate();
        Polynomial storePoly;
        res1.add(diffPoly1);

        for (int j = 0; j < i; j++) {
            res1.add(diffPoly2);
            storePoly = diffPoly2.copy();
            diffPoly2 = ManPolys.longdivision(diffPoly1, diffPoly2)[1].negateAll();
            if (diffPoly2.getSize() == 1) {
                res1.add(diffPoly2);
                sturmSequence = res1;
                return;
            }
            if (diffPoly2.getSize() == 0) {
                sturmSequence = res1;
                return;
            }
            diffPoly1 = storePoly.copy();
        }
        sturmSequence = res1;
        return;
    }
    
    private Rational [] evaluateSturmsequence(Rational x) {
        Rational [] result = new Rational[sturmSequence.size()];
        for (int i = 0; i < sturmSequence.size(); i++) {
            result[i] = sturmSequence.get(i).evaluatePoly(x);
        }
        return result;
    }

    /**
     * evaluates the sturmsequence for minus infinity by looking at the highest
     * exponents.
     * Returns a list of the evaluation of every polynomial in the sequence
     * @return Array of Rationals
     */
    public Rational [] SturmsequenceMinusInf() {
        Rational [] result = new Rational[sturmSequence.size()];
        for (int i = 0; i < sturmSequence.size(); i++) {
            int deg = sturmSequence.get(i).getDegree();
            Rational coeff = sturmSequence.get(i).coefficients[deg];
            if (deg % 2 == 0) {
                // if leading coefficient is even
                //   - negative coefficient stays negative
                //   - positive coefficient stays positive
                result[i] = coeff;
            } else {
                // if leading coefficient is odd
                //   - negative coefficient gets positive
                //   - positive coefficient gets negative
                result[i] = coeff.negate();
            }
        }
        return result;
    }

    /**
      evaluates the sturmsequence for infinity by looking at the highest
     * exponents.
     * Returns a list of the evaluation of every polynomial in the sequence
     * @return Array of Rationals
     */
    public Rational [] SturmsequenceInf() {
        Rational [] result = new Rational[sturmSequence.size()];
        // highest coefficient decides always divergence
        for (int i = 0; i < sturmSequence.size(); i++) {
            int deg = sturmSequence.get(i).getDegree();
            Rational coeff = sturmSequence.get(i).coefficients[deg];
            result[i] = coeff;
        }
        return result;
    }

    /**
     * returns the number of the root of an algebraic number.
     * @return rootID
     */
    public int numberOfRoot() {
        Rational [] sturmSequenceup = evaluateSturmsequence(interval[1]);
        return SignChangeCounter(SturmsequenceMinusInf()) - SignChangeCounter(sturmSequenceup);
    }

    /**
     * returns the number of total roots in the interval.
     * @return number of roots
     */
    public int rootsInInterval() {
        Rational [] sturmSequencedown = evaluateSturmsequence(interval[0]);
        Rational [] sturmSequenceup = evaluateSturmsequence(interval[1]);
        return SignChangeCounter(sturmSequencedown) - SignChangeCounter(sturmSequenceup);
    }

    private int rootsOfPoly() {
        Rational [] sturmSequencedown = SturmsequenceMinusInf();
        Rational [] sturmSequenceup = SturmsequenceInf();
        return SignChangeCounter(sturmSequencedown) - SignChangeCounter(sturmSequenceup);
    }

    private int SignChangeCounter(Rational [] sturmSequence) {
        int counter = 0;
        boolean negative = false;
        if (sturmSequence.length == 0) {
            return 0;
        }
        if (sturmSequence[0].isNegative()) {
            negative = true;
        }
        for (int i = 1; i < sturmSequence.length; i++) {
            if (sturmSequence[i].isNegative()  & !negative) {
                counter += 1;
                negative = true;
            }
            if (!sturmSequence[i].isNegative() & negative) {
                counter += 1;
                negative = false;
            }
        }
        return counter;
    }

    /**
     * fatorization of an integer i
     * @param i int number to be factorized
     * @return list of integer / factors of i
     */
    public List<Integer> factors(int i) {
        List<Integer> result = new ArrayList<>();
        if (i < 0) {
            i = -i;
        }
        if (i == 0) {
            result.add(0);
        }
        for (int j = 1; j <= i; j++) {
            if (i % j == 0) {
                result.add(j);
                result.add(-j);
            }
        }
        return result;
    }

    private Rational [] listToRational(Integer [] intList) {
        Rational [] result = new Rational[intList.length];
        for (int i = 0; i < intList.length; i++) {
            result[i] = Rational.valueOf(intList[i], 1);
        }
        return result;
    } 

    /**
     * Lagrange interpolating formula polynomial algorithm
     * Function that gets a list of nodes and a list of values and interpolates 
     * the points given by the lists
     * the algorithm computes a polynomial such that for every index
     * i in nodes and values p(nodes(i)) = values(i)
     * nodes and values should have the same length
     * @param nodes x values of the points
     * @param values p(x) values of the points
     * @return polynomial p that interpolates the points
     */
    public Polynomial lagrangePolynomial (Rational [] nodes, Rational [] values, int grad) {
        // build polynomial
        Polynomial result = new Polynomial();
        if (grad == 1) {
            Rational[] coff = new Rational[2];
            coff[0] = nodes[0].negate().add(values[0]);
            coff[1] = Rational.valueOf(1, 1);
            return new Polynomial(coff);
        }
        for (int j = 0; j < grad; j++) {
            // for every j in nodes build the kronecker delta l_j(x_m)
            // while m is going through the nodes without the j-th element
            Polynomial p = new Polynomial();
            // var product keeps track of the denominator (x_j - x_m)
            // and stores it until the polynomial is complete
            Rational product = Rational.valueOf(1, 1);

            for (int m = 0; m < grad; m++) {
                if (m == j) {
                    continue;
                }
                // build nominator

                Rational [] list = new Rational[2];
                // build polynomial x-x_m
                list[0] = nodes[m].negate();
                list[1] = Rational.valueOf(1, 1);
                Polynomial r = new Polynomial(list);

                // multiply iteratively x-x_m to polynomial p for every m
                p = ManPolys.multiplyLinear(p, r);
                
                // build denominator (calculate (x_j - x_m))
                product = nodes[j].sub(nodes[m]).mul(product);
            }
            // Add this Polynomial to the sum of all polynomials
            p = p.mul(product.inverse());
            result = ManPolys.addPolynomials(result, p.mul(values[j]));
        }
        // return sum of polynomials (also a polynomial)
        return result;
    }

    /**
     * Factorizes the Polynomial once and returns an array of size 2
     * with the two factors of the polynomial.
     * If the polynomial is irreducible the function returns the polynomial itself
     * on position 0 and an empty polynomial at position 1
     * Only works on integer polynomials!
     * @return Array of two polynomial factors
     */
    public Polynomial [] factorizePolynomial() {
        // initialize with original polynomial and empty polynomial
        Polynomial [] result = new Polynomial[2];
        result[0] = polynomial;
        result[1] = new Polynomial();

        // if there is a factor,
        // there is at least a factor of maximum degree deg/2
        int maxdeg = polynomial.getSize() / 2;

        // if polynomial linear of constant return original
        if (polynomial.getSize() <= 2) {
            return result;
        }

        // generate maxdeg + 1 points of the polynomial
        // take the maxdeg + 1 points that are closest to zero
        Integer [] nodes = new Integer[maxdeg + 1];
        for (int i = 0; i < maxdeg + 1; i++) {
            if (i == 0) {
                nodes[i] = 0;
                continue;
            }
            if (i % 2 == 1) {
                nodes[i] = i/2 + 1;
            }
            if (i % 2 == 0) {
                nodes[i] = -i/2;
            }
        }
        // get values by evaluating the polynomial on the nodes
        List<Integer> values = new ArrayList<>();
        for (int i = 0; i < nodes.length; i++) {
            Rational val = polynomial.evaluatePoly(Rational.valueOf(nodes[i], 1));
            // if values are zero -> already found a linear factor
            if (val == Rational.ZERO) {
                Rational[] coeffs = new Rational[2];
                coeffs[0] = Rational.valueOf(-nodes[i],1);
                coeffs[1] = Rational.valueOf(1, 1);
                Polynomial linearfactor = new Polynomial(coeffs);
                result[0] = linearfactor;
                result[1] = ManPolys.longdivision(polynomial, linearfactor)[0];
                return result;
            }
            //Assume val is integral (is integral because polynomial has int coefficients)
            Integer intval = val.mNum;
            //Assert.assertTrue(val.isIntegral());
            values.add(intval);
        }
        // for every node make a list of factors of the value
        List<List<Integer>> factorslist = new ArrayList<>();
        for (int i = 0; i < values.size(); i++) {
            factorslist.add(factors(values.get(i)));
        }
        // choose a value for each node
        // make a lagrange polynomial
        // test if its a factor of p
        for (int i = 0; i <= maxdeg; i++) {
            Polynomial [] p = generateFactor(factorslist, nodes, i+1);
            // if degree is smaller than original polynomial this is a factor
            if (p[0].getDegree() < polynomial.getDegree()) {
                // factor found
                return p;
            }
        }
        return result;
    }

    /**
     * 
     * @param possibleValues
     * @param nodes
     * @param m
     * @return Generates a polynomial that is a factor of the algebraic number
     */
    /*
    public Polynomial [] generateFactorOLd(List<List<Integer>> possibleValues, Integer [] nodes, int m) {
        // initialize counter
        Integer [] counter = new Integer[possibleValues.size()];
        for (int i = 0; i < possibleValues.size(); i++) {
            counter[i] = 0;
        }
        Integer [] maxvalues = new Integer[possibleValues.size()];
        for (int i = 0; i < possibleValues.size(); i++) {
            maxvalues[i] = possibleValues.get(i).size()-1;
        }
        // initialize polynomial
        Polynomial testPolynomial = new Polynomial();
        Rational [] nodesRat = listToRational(nodes);
        // check polynomial of zeros as index for values
        Integer [] testValues = new Integer[possibleValues.size()];
        Polynomial [] division = new Polynomial[2];
        Polynomial [] result = new Polynomial[2];
        // create testValues
        while (true) {
            testValues = new Integer[possibleValues.size()];
            for (int k = 0; k < possibleValues.size(); k++) {
                testValues[k] = possibleValues.get(k).get(counter[k]);
            }

            testPolynomial = lagrangePolynomial(nodesRat, listToRational(testValues), m);
            //System.out.println(Arrays.toString(testPolynomial.coefficients));
            //Rational [] test = new Rational[3];
            //test[0] = Rational.valueOf(49,1);
            //test[1] = Rational.valueOf(42,1);
            //test[2] = Rational.valueOf(1,1);
            //testPolynomial = new Polynomial(test);
            division = ManPolys.longdivision(polynomial, testPolynomial);
            if (division[1].getSize() == 0) {
                testPolynomial = testPolynomial.removeZeros();
                if (testPolynomial.getDegree() == m) {
                    result[0] = testPolynomial;
                    result[1] = division[0];
                    return result;
                }
            }
            counter = CounterIncrease(counter, maxvalues);
            counter = CounterIncrease(counter, maxvalues);
            if (counter[0] == -1) {
                result[0] = polynomial;
                result[1] = new Polynomial();
                return result;
            }
        }
    }*/

    /**
     * 
     * @param possibleValues
     * @param nodes
     * @param m
     * @return Generates a polynomial that is a factor of the algebraic number
     */
    private Polynomial [] generateFactor(List<List<Integer>> possibleValues, Integer [] nodes, int m) {
        // initialize a counter
        // each cell counts to its own maxvalue in maxvalues
        Integer [] counter = new Integer[m];
        for (int i = 0; i < m; i++) {
            counter[i] = 0;
        }
        Integer [] maxvalues = new Integer[m];
        for (int i = 0; i < m; i++) {
            maxvalues[i] = possibleValues.get(i).size()-1;
        }
        // initialize polynomial
        Polynomial testPolynomial = new Polynomial();
        Rational [] nodesRat = listToRational(nodes);
        // check polynomial of zeros as index for values
        Integer [] testValues;
        Polynomial [] division = new Polynomial[2];
        Polynomial [] result = new Polynomial[2];
        // go threw all testvalues in possible value combinations
        while (true) {
            testValues = new Integer[m];
            for (int k = 0; k < m; k++) {
                testValues[k] = possibleValues.get(k).get(counter[k]);
            }

            testPolynomial = lagrangePolynomial(nodesRat, listToRational(testValues), m);
            if (m == 3) {
                //System.out.println(Arrays.toString(testPolynomial.coefficients));
                if (testValues[0] == 49 && testValues[1] == 8 && testValues[2] == 92) {
                    System.out.println("ok");
                    System.out.println(Arrays.toString(testPolynomial.coefficients));
                }
            }
            //System.out.println(Arrays.toString(polynomial.coefficients));
            //System.out.println("durch");
            //System.out.println(Arrays.toString(testPolynomial.coefficients));
            //System.out.println("ist");
            //Rational [] test = new Rational[3];
            //test[0] = Rational.valueOf(49,1);
            //test[1] = Rational.valueOf(42,1);
            //test[2] = Rational.valueOf(1,1);
            //testPolynomial = new Polynomial(test);
            division = ManPolys.longdivision(polynomial, testPolynomial);
            // if poly is divisible by factor and factor is not constant
            // a factor is found
            if (division[1].getSize() == 0) {
                testPolynomial = testPolynomial.removeZeros();
                // non constant
                if (testPolynomial.getDegree() >= 1) {
                    result[0] = testPolynomial;
                    result[1] = division[0];
                    return result;
                }
            }
            //counter = CounterIncrease(counter, maxvalues);
            counter = CounterIncrease(counter, maxvalues);
            if (counter[0] == -1) {
                result[0] = polynomial;
                result[1] = new Polynomial();
                return result;
            }
        }
    }

    private Integer [] CounterIncrease(Integer [] count, Integer [] maxvalues) {
        if (count[0] == -1) {
            return count;
        }
        for (int i = 0; i < count.length; i++) {
            if (count[i] < maxvalues[i]) {
                // add one and return
                count[i] = count[i] + 1;
                return count;
            } else {
                // reset to zero
                count[i] = 0;
                // if end return -1
                if (i == count.length - 1) {
                    Integer [] end = new Integer[1];
                    end[0] = -1;
                    return end;
                }
            }
        }
        return count;
    }

    private static Rational [] addIntervals(Rational[] interval1, Rational[] interval2) {
        Rational [] result = new Rational[2];
        result[0] = interval1[0].add(interval2[0]);
        result[1] = interval1[1].add(interval2[1]);
        return result;
    }

    private static Rational [] divideIntervals(Rational[] interval1, Rational[] interval2) {
        Rational [] result = new Rational[2];
        Rational[] minsearch = new Rational[4];
        minsearch[0] = interval1[0].mul(interval2[0].inverse());
        minsearch[1] = interval1[0].mul(interval2[1].inverse());
        minsearch[2] = interval1[1].mul(interval2[0].inverse());
        minsearch[3] = interval1[1].mul(interval2[1].inverse());

        Rational intervaldown = minsearch[0];
        Rational intervalup = minsearch[0];
        
        for (int i = 0; i < 4; i++) {
            // minsearch[i] > intervalup
            if (intervalup.sub(minsearch[i]).isNegative()) {
                intervalup = minsearch[i];
            }
            // minsearch[i] < intervaldown
            if (minsearch[i].sub(intervaldown).isNegative()) {
                intervaldown = minsearch[i];
            }
        }
        result[0] = intervaldown;
        result[1] = intervalup;
        return result;
    }

    /**
     * adds two algebraic numbers
     * @param a algebraic number
     * @param b algebraic number
     * @return sum of a and b
     */
    public static AlgebraicNumbers add(AlgebraicNumbers a, AlgebraicNumbers b) {
        a = a.minimize();
        b = b.minimize();
        System.out.println(a);
        System.out.println(b);

        if (a.isZero()) {
            return b;
        }
        if (b.isZero()) {
            return a;
        }
        // initialization
        BivariatePolynomial f;
        BivariatePolynomial g;
        // turn the smaller polynomial to g(x-y)
        if (a.polynomial.getSize() < b.polynomial.getSize()) {
            f = b.polynomial.toBivariate();
            g = BivariatePolynomial.subxy(a.polynomial);
        } else {
            f = a.polynomial.toBivariate();
            g = BivariatePolynomial.subxy(b.polynomial);
        }

        while (f.coefficients.length > 1 && g.coefficients.length > 1) {
            if (g.coefficients.length > f.coefficients.length) {
                // divide g by gcd of coefficients of g
                //g = ManPolys.reduce(g);
                g = ManPolys.pseudoMod(g, f);
            } else {
                // divide f by gcd of coefficients of f
                //f = ManPolys.reduce(f);
                f = ManPolys.pseudoMod(f, g);
            }
        }
        
        // output calculation
        Polynomial resPoly;
        if (f.coefficients.length < g.coefficients.length) {
            resPoly = new Polynomial(f.coefficients[0]);
        } else {
            resPoly = new Polynomial(g.coefficients[0]);
        }
        // interval calculation
        Rational [] intervalRes = addIntervals(a.interval, b.interval);
        AlgebraicNumbers r = new AlgebraicNumbers(resPoly, intervalRes[0], intervalRes[1]);
        while (resPoly.numberOfRootsinInterval(intervalRes) > 1) {
            a = a.improveInterval();
            b = b.improveInterval();
            intervalRes = addIntervals(a.interval, b.interval);
        }

        // return
        AlgebraicNumbers result = new AlgebraicNumbers(resPoly, intervalRes[0], intervalRes[1]);
        result = result.minimize();
        return result;
    }

    public static AlgebraicNumbers divide(AlgebraicNumbers a, AlgebraicNumbers b) {
        //a = a.minimize();
        //b = b.minimize();
        if (a.isZero()) {
            return AlgebraicNumbers.ZERO;
        }
        if (b.isZero()) {
            //Assert error
        }

        BivariatePolynomial f = b.polynomial.toBivariate();
        BivariatePolynomial g = BivariatePolynomial.mulxy(a.polynomial);

        while (f.coefficients.length > 1 && g.coefficients.length > 1) {
            if (g.coefficients.length > f.coefficients.length) {
                //g = ManPolys.reduce(g);
                g = ManPolys.pseudoMod(g, f);
            } else {
                //f = ManPolys.reduce(f);
                f = ManPolys.pseudoMod(f, g);
            }
            //f = f.removeZeros();
            //g = g.removeZeros();
        }
        
        // output calculation
        Polynomial resPoly;
        if (f.coefficients.length < g.coefficients.length) {
            resPoly = new Polynomial(f.coefficients[0]);
        } else {
            resPoly = new Polynomial(g.coefficients[0]);
        }

        // interval calculation
        Rational [] intervalRes = divideIntervals(a.interval, b.interval);
        //resPoly.numberOfRootsinInterval(intervalRes) > 1
        while (resPoly.numberOfRootsinInterval(intervalRes) > 1) {
            a = a.improveInterval();
            b = b.improveInterval();
            intervalRes = divideIntervals(a.interval, b.interval);
        }

        AlgebraicNumbers result = new AlgebraicNumbers(resPoly, intervalRes[0], intervalRes[1]);
        result = result.makeUnique();
        return result;
    }

    public static AlgebraicNumbers multiply(AlgebraicNumbers a, AlgebraicNumbers b) {
        if (a.isZero() || b.isZero()) {
            return AlgebraicNumbers.ZERO;
        }
        AlgebraicNumbers oneOverb = b.inverse();
        return AlgebraicNumbers.divide(a, oneOverb);
    }

    public static AlgebraicNumbers mulConst(AlgebraicNumbers a, Rational constant) {
        if (constant == Rational.ZERO || a.isZero()) {
            return AlgebraicNumbers.ZERO;
        }
        // variable pote to build e^i iteratively
        Rational inverseConstant = constant.inverse();
        Rational pote = Rational.valueOf(1, 1);
        Rational [] coeff = new Rational[a.polynomial.getSize()];

        for (int i = 0; i < coeff.length; i++) {
            coeff[i] = pote.mul(a.polynomial.coefficients[i]);
            pote = pote.mul(inverseConstant);
        }
        Polynomial resultPoly = new Polynomial(coeff);
        Rational [] intervalresult = new Rational[2];
        intervalresult[0] = a.interval[0].mul(constant);
        intervalresult[1] = a.interval[1].mul(constant);
        AlgebraicNumbers resultAlg;
        if (constant.isNegative()) {
            resultAlg = new AlgebraicNumbers(resultPoly, intervalresult[1], intervalresult[0]);
        } else {
            resultAlg = new AlgebraicNumbers(resultPoly, intervalresult[0], intervalresult[1]);
        }
        resultAlg = resultAlg.makeUnique();
        return resultAlg;
    }

    public static AlgebraicNumbers minus(AlgebraicNumbers a, AlgebraicNumbers b) {
        AlgebraicNumbers minusb = b.negate();
        return AlgebraicNumbers.add(a, minusb);
    }

    /**
     * minimizes the algebraic number by:
     * - removing the zero roots
     * - remove multiple roots
     * - normalize polynomial (make all coefficients to int)
     * - factorize the polynomial and choose the factor 
     * containing the root
     * @return minimized algebraic number
     * (not yet unique) coefficients could be different by constant factors
     */
    public AlgebraicNumbers minimize() {
        // test if already min
        AlgebraicNumbers r = this;
        r = r.removeZeroNodes();
        r = r.squareFree();
        r = r.normalize();
        Polynomial [] fact = r.factorizePolynomial();
        AlgebraicNumbers a = new AlgebraicNumbers(r.polynomial, interval[0], interval[1]);
        while (fact[1].getSize() != 0) {
            a = new AlgebraicNumbers(fact[0], interval[0], interval[1]);
            if (a.rootsInInterval() == 0) {
                a = new AlgebraicNumbers(fact[1], interval[0], interval[1]);
            }
            fact = a.factorizePolynomial();
        }
        return a;
        
        //if this is zero: fact[0].evaluatePolyAlgebraic(this);
        //create alg number with poly fact[0]
        //continue with this (end if fact[1].getSize() == 0)
    }

    /**
     * make all to int
     */
    private AlgebraicNumbers normalize() {
        if (polynomial.getSize() == 0) {
            return this;
        }
        Rational g = polynomial.coefficients[0];
        for (int i = 1; i < polynomial.getSize(); i++) {
            g = g.gcd(polynomial.coefficients[i]);
        }
        Polynomial result = polynomial.mul(g.inverse());
        return new AlgebraicNumbers(result, interval[0], interval[1]);
    }

    /**
     * remove the zero roots
     * @return polynomial divided by x**i with i amount of zero nodes
     */
    public AlgebraicNumbers removeZeroNodes() {
        if (!isZero()) {
            Polynomial c;
            c = polynomial.reverse().removeZeros().reverse();
            return new AlgebraicNumbers(c, interval[0], interval[1]);
        } else {
            return AlgebraicNumbers.ZERO;
        }
    }

    /**
     * minimize and make highest coeff to one
     * @return minimal algebraic number 
     * (unique because highest coeff is fixed to be 1)
     */
    public AlgebraicNumbers makeUnique() {
        if (polynomial.getSize() == 0) {
            return this;
        }
        AlgebraicNumbers a = minimize();
        Rational g = a.polynomial.coefficients[a.polynomial.getDegree()].inverse();
        Polynomial result = a.polynomial.mul(g);
        return new AlgebraicNumbers(result, interval[0], interval[1]);
    }

    /**
     * Test if the algebraic number is zero.
     * An Algebraic number is zero iff:
     * - interval contains zero
     * - polynomial has root zero
     * @return true iff algebraic number is zero
     */
    public Boolean isZero() {
        if (polynomial.getSize() == 0) {
            return true;
        }
        if (polynomial.coefficients[0] == Rational.ZERO) {
            if (interval[0].isNegative() && !interval[1].isNegative()) {
                return true;
            }
        }
        return false;
    }

    /**
     * greater relation on algebraic numbers
     * @param o
     * @return true iff this is greater than o
     */
    public boolean greater(Object o) {
        if (o instanceof AlgebraicNumbers) {
            AlgebraicNumbers a1 = (AlgebraicNumbers) o;
            AlgebraicNumbers a2 = this;
            if (a1.equals(a2)) {
                return false;
            }
            // if intervals are not disjoint either
            // - intervalup of a1 is greater than intervaldown of self
            // - intervalup of self is greater than intervaldown of a1

            // a1 up is smaller than a2 down -> negative
            Rational a1smaller = a1.interval[1].sub(a2.interval[0]);
            // a2 up is smaller than a1 down -> negative
            Rational a2smaller = a2.interval[1].sub(a1.interval[0]);
            // while one is not completely bigger than the other improve
            while (!(a1smaller.isNegative() || a2smaller.isNegative())) {
                a1 = a1.improveInterval();
                a2 = a2.improveInterval();
                a1smaller = a1.interval[1].sub(a2.interval[0]);
                a2smaller = a2.interval[1].sub(a1.interval[0]);
            }
            // if upper bound of o is smaller than lower bound of self then self is greater
            Rational difference = a1.interval[1].sub(a2.interval[0]);
            if (difference.isNegative() || difference == Rational.ZERO) {
                return true;
            } else {
                return false;
            }
        }
        return false;
    }

    /**
     * smaller relation on algebraic numbers
     * @param o
     * @return true iff this is smaller than o
     */
    public boolean smaller(Object o) {
        if (o instanceof AlgebraicNumbers) {
            if (this.equals(o)) {
                return false;
            }
            if (this.greater(0)) {
                return false;
            }
            return true;
        }
        return false;
    }

    /**
     * equality relation on algebraic numbers
     * @param o
     * @return true iff this is equal to o
     */
    public boolean equals(Object o) {
        if (o instanceof AlgebraicNumbers) {
            AlgebraicNumbers a1 = (AlgebraicNumbers) o;
            AlgebraicNumbers a2 = this;
            // make o unique
            a1 = a1.makeUnique();
            // make self unique
            a2 = a2.makeUnique();
            if (a2.polynomial.equals(a1.polynomial)) {
                System.out.println("true");
                if (a2.numberOfRoot() == a1.numberOfRoot()) {
                    System.out.println("true");
                    return true;
                }
            }
        }
        return false;
    }

    public int hashCode() {
        return makeUnique().polynomial.hashCode();
    }


    public final static AlgebraicNumbers ZERO = new AlgebraicNumbers(
        new Polynomial(), Rational.ZERO, Rational.valueOf(1, 1));
}
