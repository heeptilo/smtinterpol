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

    public String toString() {
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
        result += " [" + interval[0] + ":" + interval[1] + ")";
        result += " (" + numberOfNode() + ")";
        if (rootsInInterval() > 1) {
            result += " not unique!";
        }
        return result;
    }

    public AlgebraicNumbers improveInterval() {
        Rational midInterval = interval[0].add(interval[1]).div(Rational.valueOf(2, 1));
        AlgebraicNumbers a = new AlgebraicNumbers(polynomial, interval[0], midInterval);
        if (a.rootsInInterval() == 1) {
            return a;
        } else {
            return new AlgebraicNumbers(polynomial, midInterval, interval[1]);
        }
    }
    
    public AlgebraicNumbers inverse() {
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
        // calculate new interval wrt. the < relation
        Rational idown;
        Rational iup;
        idown = interval[1].negate();
        iup = interval[0].negate();
        AlgebraicNumbers neg = new AlgebraicNumbers(polynomial.negate(), idown, iup);
        return neg;
    }

    /**
     * Function squareFree takes no arguments and manipulates the polynomial such
     * that it represents the same roots but every root just once. 
     */
    public AlgebraicNumbers squareFree() {
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

    public void BuildSturmSequence() {
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
    
    public Rational [] evaluateSturmsequence(Rational x) {
        Rational [] result = new Rational[sturmSequence.size()];
        for (int i = 0; i < sturmSequence.size(); i++) {
            result[i] = sturmSequence.get(i).evaluatePoly(x);
        }
        return result;
    }

    public Rational [] SturmsequenceMinusInf() {
        Rational [] result = new Rational[sturmSequence.size()];
        for (int i = 0; i < sturmSequence.size(); i++) {
            int deg = sturmSequence.get(i).getDegree();
            Rational coeff = sturmSequence.get(i).coefficients[deg];
            if (deg % 2 == 0) {
                result[i] = coeff;
            } else {
                result[i] = coeff.negate();
            }
        }
        return result;
    }

    public int numberOfNode() {
        Rational [] sturmSequenceup = evaluateSturmsequence(interval[1]);
        return SignChangeCounter(SturmsequenceMinusInf()) - SignChangeCounter(sturmSequenceup) - 1;
    }

    public int rootsInInterval() {
        Rational [] sturmSequencedown = evaluateSturmsequence(interval[0]);
        Rational [] sturmSequenceup = evaluateSturmsequence(interval[1]);
        return SignChangeCounter(sturmSequencedown) - SignChangeCounter(sturmSequenceup);
    }

    public int SignChangeCounter(Rational [] sturmSequence) {
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

    public Rational [] listToRational(Integer [] intList) {
        Rational [] result = new Rational[intList.length];
        for (int i = 0; i < intList.length; i++) {
            result[i] = Rational.valueOf(intList[i], 1);
        }
        return result;
    } 

    /**
     * Lagrange interpolating polynomial algorithm
     * Function that gets a list of nodes and a list of values and interpolates 
     * the points given by the lists
     * the algorithm computes a polynomial such that for every index
     * i in nodes and values p(nodes(i)) = values(i)
     * nodes and values should have the same length
     * @param nodes x values of the points
     * @param values p(x) values of the points
     * @return polynomial p that interpolates the points
     */
    public Polynomial lagrangePolynomial (Rational [] nodes, Rational [] values) {
        // build polynomial
        Polynomial result = new Polynomial();
        if (nodes.length == 1) {
            Rational[] coff = new Rational[2];
            coff[0] = nodes[0].negate().add(values[0]);
            coff[1] = Rational.valueOf(1, 1);
            return new Polynomial(coff);
        }
        for (int j = 0; j < nodes.length; j++) {
            // for every j in nodes build the kronecker delta l_j(x_m)
            // while m is going through the nodes without the j-th element
            Polynomial p = new Polynomial();
            // var product keeps track of the denominator (x_j - x_m)
            // and stores it until the polynomial is complete
            Rational product = Rational.valueOf(1, 1);

            for (int m = 0; m < nodes.length; m++) {
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

    /**only works on ints change to find divisor*/
    public Polynomial [] factorizePolynomial() {
        System.out.println(Arrays.toString(polynomial.coefficients));
        Polynomial [] result = new Polynomial[2];
        result[0] = polynomial;
        result[1] = new Polynomial();
        // if there is a factor,
        // there is at least a factor of maximum degree deg/2
        int maxdeg = polynomial.getDegree() / 2;
        if (maxdeg == 0) {
            return result;
        }

        // generate maxdeg + 1 points of the polynomial
        // take the maxdeg + 1 points that are closest to zero
        Integer [] nodes = new Integer[maxdeg];
        for (int i = 0; i < maxdeg; i++) {
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

        List<Integer> values = new ArrayList<>();
        for (int i = 0; i < nodes.length; i++) {
            Rational val = polynomial.evaluatePoly(Rational.valueOf(nodes[i], 1));
            //Assume val is integral
            Integer intval = val.mNum;
            //Assert.assertEquals(val.isIntegral());
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
        //Polynomial p = generateFactor(factorslist, nodes, maxdeg);
        for (int i = 0; i < maxdeg; i++) {
            Polynomial [] p = generateFactor(factorslist, nodes, i+1);
            if (p[0].getDegree() == i+1) {
                // factor found
                return p;
            }
        }
        return result;
        //polynomialFactors.add(p);
        //polynomialFactors.add(ManPolys.longdivision(polynomial, p).get(0));
    }

    /**
     * 
     * @param remainfactors
     * @param nodes
     * @param m
     * @return Generates a polynomial that is a factor of the algebraic number
     */
    public Polynomial [] generateFactor(List<List<Integer>> remainfactors, Integer [] nodes, int m) {
        // initialize counter
        Integer [] counter = new Integer[remainfactors.size()];
        for (int i = 0; i < remainfactors.size(); i++) {
            counter[i] = 0;
        }
        Integer [] maxvalues = new Integer[remainfactors.size()];
        for (int i = 0; i < remainfactors.size(); i++) {
            maxvalues[i] = remainfactors.get(i).size()-1;
        }
        // initialize polynomial
        Polynomial testPolynomial = new Polynomial();
        Rational [] nodesRat = listToRational(nodes);
        // check polynomial of zeros as index for values
        Integer [] testValues = new Integer[remainfactors.size()];
        Polynomial [] division = new Polynomial[2];
        Polynomial [] result = new Polynomial[2];
        // create testValues
        while (true) {
            testValues = new Integer[remainfactors.size()];
            for (int k = 0; k < remainfactors.size(); k++) {
                testValues[k] = remainfactors.get(k).get(counter[k]);
            }

            testPolynomial = lagrangePolynomial(nodesRat, listToRational(testValues));
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
            //counter = CounterIncrease(counter, maxvalues);
            if (counter[0] == -1) {
                result[0] = polynomial;
                result[1] = new Polynomial();
                return result;
            }
        }
    }

    public Integer [] CounterIncrease(Integer [] count, Integer [] maxvalues) {
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

    public static Rational [] addIntervals(Rational[] interval1, Rational[] interval2) {
        Rational [] result = new Rational[2];
        result[0] = interval1[0].add(interval2[0]);
        result[1] = interval1[1].add(interval2[1]);
        return result;
    }

    public static Rational [] divideIntervals(Rational[] interval1, Rational[] interval2) {
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

    public static AlgebraicNumbers add(AlgebraicNumbers a, AlgebraicNumbers b) {
        a = a.minimize();
        b = b.minimize();

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
                g = ManPolys.divideBiPoly(g, f);
            } else {
                f = ManPolys.divideBiPoly(f, g);
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
        a = a.minimize();
        b = b.minimize();
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
                g = ManPolys.divideBiPoly(g, f);
            } else {
                f = ManPolys.divideBiPoly(f, g);
            }
            f = f.removeZeros();
            g = g.removeZeros();
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
        result = result.minimize();
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
        AlgebraicNumbers resultAlg = new AlgebraicNumbers(resultPoly, intervalresult[0], intervalresult[1]);
        return resultAlg;
    }

    public static AlgebraicNumbers minus(AlgebraicNumbers a, AlgebraicNumbers b) {
        AlgebraicNumbers minusb = b.negate();
        return AlgebraicNumbers.add(a, minusb);
    }

    
    public AlgebraicNumbers minimize() {
        // test if already min
        removeZeroNodes();
        normalize();
        Polynomial [] fact = factorizePolynomial();
        AlgebraicNumbers a = new AlgebraicNumbers(polynomial, interval[0], interval[1]);
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

    public AlgebraicNumbers normalize() {
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

    public AlgebraicNumbers removeZeroNodes() {
        if (!isZero()) {
            Polynomial c;
            c = polynomial.reverse().removeZeros().reverse();
            return new AlgebraicNumbers(c, interval[0], interval[1]);
        } else {
            return AlgebraicNumbers.ZERO;
        }
    }

    public AlgebraicNumbers makeUnique() {
        if (polynomial.getSize() == 0) {
            return this;
        }
        Rational g = polynomial.coefficients[polynomial.getDegree()].inverse();
        AlgebraicNumbers a = minimize();
        Polynomial result = a.polynomial.mul(g);
        return new AlgebraicNumbers(result, interval[0], interval[1]);

    }

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
/*
    public boolean equals(Object o) {
        if (o instanceof AlgebraicNumbers) {
            AlgebraicNumbers a1 = (AlgebraicNumbers) o;
            AlgebraicNumbers amin = AlgebraicNumbers.minus(this, a1);
            if (amin.isZero()) {
                return true;
            } else {
                return false;
            }
        }
    }
    */

    public final static AlgebraicNumbers ZERO = new AlgebraicNumbers(
        new Polynomial(), Rational.ZERO, Rational.valueOf(1, 1));
}
