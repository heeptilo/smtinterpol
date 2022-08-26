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

import java.util.*;

/**
This class represents polynomials.
A polynomial is defined by its coefficients, a List of Rationals where
the coefficient of x**i has index i.
 *
 * @author Tilo Heep
 */
public class Polynomial {
    /**
	 * The list of coefficients of the polynomial 
	 */
    Rational [] coefficients;

    /**
     * constructor with List of Rationals as coefficients
     * @param coeff
     */
    public Polynomial(Rational [] coeff) {
        coefficients = coeff;
    }

    /**
     * constructor with no parameters to create a polynomial
     * with an empty list of coefficients
     */
    public Polynomial() {
        Rational [] coeff = {};
        coefficients = coeff;
    }

    public Rational [] getCoefficients() {
        return coefficients;
    }

    public int getDegree() {
        return coefficients.length - 1;
    }

    public int getSize() {
        return coefficients.length;
    }

    /**
     * Function to differentiate a polynomial
     * Returns a polynomial
     * @return differentiated Polynomial
     */
    public Polynomial differentiate() {
        if (getSize() == 0) {
            return this;
        }
        if (getSize() == 1) {
            return new Polynomial();
        }
        Rational [] result = new Rational[getDegree()];
        for (int i = 0; i < getDegree(); i++ ){
            result[i] = coefficients[i+1].mul(Rational.valueOf(i + 1, 1));
        }
        Polynomial res = new Polynomial(result);
        return res;
    }

    /**
     * Function that orders the coefficients in the reverse order
     * @return reversed Polynomial
     */
    public Polynomial reverse() {
        Rational [] result = new Rational[getSize()];
        if (getSize() == 0) {
            Polynomial res = new Polynomial(result);
            return res;
        }
        int m = getSize();
        for (int i = 1; i < m + 1; i++ ) {
            result[i-1] = coefficients[m-i];
        }
        Polynomial res = new Polynomial(result);
        return res;
    }

    /**
     * Function that removes the zeros if there are any at the position of the highest exponents
     * @return The reduced Polynomial
     */
    public Polynomial removeZeros() {
        List<Rational> coeff = new ArrayList<>();
        if (getSize() == 0) {
            return new Polynomial();
        }
        for (int i = 0; i < getSize(); i++) {
            coeff.add(coefficients[getSize() - i - 1]);
        }
        int deletions = 0;
        while (coeff.size() != 0) {
            if (coeff.get(0) == Rational.ZERO) {
                deletions += 1;
                coeff.remove(0);
            } else {
                break;
            }
        }
        Rational [] coefflist = new Rational[getSize() - deletions];
        for (int i = 0; i < getSize() - deletions; i++) {
            coefflist[i] = coeff.get(i);
        }
        Polynomial result = new Polynomial(coefflist);
        result = result.reverse();
        return result;
    }

    /**
     * Function that returns for a polynom p(x) the polynom p(-x)
     * @return
     */
    public Polynomial negate() {
        int m = getSize();
        Rational [] result = new Rational[m];
        // If coefficient stands before odd exponent -> negate coefficient
        for (int i = 0; i < m; i++) {
            if (i % 2 == 0) {
                result[i] = coefficients[i];
            } else {
                result[i] = coefficients[i].negate();
            }
        }
        Polynomial res = new Polynomial(result);
        return res;
    }

    /**
     * negate all coefficients of the polynomial
     * @return polynomial -p
     */
    public Polynomial negateAll() {
        Rational [] coeffs = new Rational[getSize()];
        for (int i = 0; i < getSize(); i++) {
            coeffs[i] = coefficients[i].negate();
        }
        Polynomial result = new Polynomial(coeffs);
        return result;
    }

    /**
     * calculates how many roots in the given interval are
     * lower bound is excluded and upper bound included
     * @param interval
     * @return number of roots in the interval (Integer)
     */
    public Integer numberOfRootsinInterval(Rational [] interval) {
        AlgebraicNumbers a1 = new AlgebraicNumbers(this, interval[0], interval[1]);
        return a1.rootsInInterval();
    }

    /**
     * evaluates a polynomial on a given rational e
     * @param e point of evaluation
     * @return rational y-value of polynomial
     */
    public Rational evaluatePoly(Rational e) {
        // variable pote to build e^i iteratively
        Rational pote = Rational.valueOf(1, 1);
        if (getSize() == 0) {
            return Rational.ZERO;
        }
        if (getSize() == 1) {
            return coefficients[0];
        }
        Rational sum = Rational.ZERO;
        sum = sum.add(coefficients[0]);
        for (int i = 1; i < getSize(); i++) {
            pote = pote.mul(e);
            sum = sum.add(coefficients[i].mul(pote));
        }
        return sum;
    }

    /**
     * evaluates a polynomial on a given algebraic number a
     * if a is a root this should return Zero(algebraic)
     * @param a algebraic number
     * @return algebraic number y-value
     */
    public AlgebraicNumbers evaluatePolyAlgebraic(AlgebraicNumbers a) {
        if (getSize() == 0) {
            // return 0
            return AlgebraicNumbers.ZERO;
        }
        if (getSize() == 1) {
            Rational [] linear = new Rational[2];
            linear[0] = coefficients[0].negate();
            linear[1] = Rational.valueOf(1, 1);
            return new AlgebraicNumbers(new Polynomial(), coefficients[0].sub(Rational.valueOf(1, 1)),
            coefficients[0].add(Rational.valueOf(1, 1)));
        }
        Rational [] con = {coefficients[0].negate(), Rational.valueOf(1, 1)};
        AlgebraicNumbers sum = new AlgebraicNumbers(new Polynomial(con), coefficients[0].sub(Rational.valueOf(1, 1)),
        coefficients[0].add(Rational.valueOf(1, 1)));
        AlgebraicNumbers pote = new AlgebraicNumbers(a.polynomial, a.interval[0], a.interval[1]);

        for (int i = 1; i <= getDegree(); i++) {
            AlgebraicNumbers constmul = AlgebraicNumbers.mulConst(pote, coefficients[i]);
            constmul = constmul.removeZeroNodes();
            sum = sum.removeZeroNodes();
            sum = AlgebraicNumbers.add(sum, constmul);
            if (i != getDegree()) {
                pote = pote.minimize();
                pote = AlgebraicNumbers.multiply(pote, a);
            }
        }
        return sum;
    }

    //
    public Polynomial copy() {
        Rational [] coeff = new Rational[getSize()];
        for (int i = 0; i < getSize(); i++) {
            coeff[i] = coefficients[i];
        }
        return new Polynomial(coeff);
    }

    /**
     * multiplies the polynomial with a given constant.
     * @param constant
     * @return constant * polynomial p
     */
    public Polynomial mul(Rational constant) {
        Rational [] coeff = new Rational[getSize()];
        for (int i = 0; i <= getDegree(); i++) {
            coeff[i] = coefficients[i].mul(constant);
        }
        Polynomial result = new Polynomial(coeff);
        return result;
    }

    public boolean equals(Object o) {
        if (o instanceof Polynomial) {
            Polynomial p = (Polynomial) o;
            if (Arrays.equals(p.coefficients, coefficients)) {
                return true;
            } else {
                return false;
            }
        } else {
            return false;
        }

    }

    /**
     * Turns the polynomial into a bivariate polynomial by
     * adding each coefficient to its own list.
     * This represents a polynomial over variable y with constant
     * polynomials over x
     * @return Bivariate Polynomial over y
     */
    public BivariatePolynomial toBivariate() {
        Rational [][] coeff = new Rational[getSize()][1];
        for (int i = 0; i < getSize(); i++) {
            Rational [] a = new Rational[1];
            a[0] = coefficients[i];
            coeff[i] = a;
        }
        return new BivariatePolynomial(coeff);
    }


    public int hashCode() {
        return Arrays.hashCode(coefficients);
    }
    
}
