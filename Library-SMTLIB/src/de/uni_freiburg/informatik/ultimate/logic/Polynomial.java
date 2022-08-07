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

    /** Function to differentiate a polynomial
     * Returns a polynomial
     */
    public Polynomial differentiate() {
        Rational [] result = new Rational[getDegree()];
        for (int i = 0; i < getDegree(); i++ ){
            result[i] = coefficients[i+1].mul(Rational.valueOf(i + 1, 1));
        }
        Polynomial res = new Polynomial(result);
        return res;
    }

    /** Function that orders the coefficients in the reverse order
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

    /** Funktion that removes the zeros if there are any at the position of the highest exponents
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

    /** Function that returns for a polynom p(x) the polynom p(-x)
    */
    public Polynomial negate() {
        int m = getSize();
        Rational [] result = new Rational[m];
        // If coefficient stands before odd exponent -> negate coefficient
        for (int i = 0; i < m; i++) {
            if (i % 2 == 0) {
                result[i] = coefficients[i];
            } else {
                result[i] = (coefficients[i].negate());
            }
        }
        Polynomial res = new Polynomial(result);
        return res;
    }

    public Polynomial negateAll() {
        Rational [] coeffs = new Rational[getSize()];
        for (int i = 0; i < getSize(); i++) {
            coeffs[i] = coefficients[i].negate();
        }
        Polynomial result = new Polynomial(coeffs);
        return result;
    }

    public Integer numberOfRootsinInterval(Rational [] interval) {
        AlgebraicNumbers a1 = new AlgebraicNumbers(this, interval[0], interval[1]);
        return a1.rootsInInterval();
    }

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

    public AlgebraicNumbers evaluatePolyAlgebraic(AlgebraicNumbers a) {
        if (getSize() == 0) {
            // return 0
            return new AlgebraicNumbers(new Polynomial(), Rational.ZERO, Rational.valueOf(1, 1));
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
            //System.out.println(sum.toString());
            //System.out.println(AlgebraicNumbers.mulConst(pote, coefficients[i]).toString());
            //System.out.println( AlgebraicNumbers.mulConst(pote, coefficients[i]).toString());
            AlgebraicNumbers constmul = AlgebraicNumbers.mulConst(pote, coefficients[i]);
            constmul = constmul.removeZeroNodes();
            System.out.println("sum:");
            System.out.println(constmul);
            System.out.println("+");
            System.out.println(sum);
            System.out.println("=");
            sum = sum.removeZeroNodes();
            sum = AlgebraicNumbers.add(sum, constmul);
            System.out.println(sum);
            //System.out.println(pote.toString());
            pote = AlgebraicNumbers.multiply(pote, a);
            //pote = pote.minimize();
        }
        return sum;
    }

    // necessery???
    public Polynomial copy() {
        Rational [] coeff = new Rational[getSize()];
        for (int i = 0; i < getSize(); i++) {
            coeff[i] = coefficients[i];
        }
        return new Polynomial(coeff);
    }

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
            return coefficients.equals(p.coefficients);
        } else {
            return false;
        }

    }

    public BivariatePolynomial toBivariate() {
        Rational [][] coeff = new Rational[getSize()][1];
        for (int i = 0; i < getSize(); i++) {
            Rational [] a = new Rational[1];
            a[0] = coefficients[i];
            coeff[i] = a;
        }
        return new BivariatePolynomial(coeff);
    }


    /* 
    public List<List<Rational>> divideBiPoly(BivariatePolynomial q) {
        Polynomial p = copy();

        // multiply coefficients (constant) with highest coefficient of q
        List<List<Rational>> extendcoeff = new ArrayList<>();
        // save the highest coefficient (will always be multiplied with restcoefficients)
        Rational [] highestCoeffq = q.coefficients[q.getDegree()];
        for (int i = 0; i < p.getSize(); i++) {
            extendcoeff.add(mulConst(highestCoeffq ,p.coefficients[i]));
        }
        // div is highest coefficient polynomial of p
        Rational div = coefficients[getDegree()];
        int degdif = extendcoeff.size() - q.getSize();
        // i iterates threw q (i + difference of degree) is the outdegree
        // -1 because the highest coefficient will be deleted anyway
        for (int i = 0; i < q.getDegree(); i++) {
            List<Rational> subcoeff = mulConst(q.coefficients[i], div);
            extendcoeff.set(i, minusList(extendcoeff.get(i), subcoeff));
        }
        extendcoeff.remove(q.getDegree());

        int degp = extendcoeff.size();
        int degq = q.getSize() - 1;

        while (degp > degq) {
            // leading coefficient / not necessery to divide because of extension
            List<Rational> difference = extendcoeff.get(degp - 1);

            // from lowest possible coefficient in p such that q * div 
            // has the same exponent iterate to the end
            // no quotient needed else add div to quotient
            for ( int i = 0; i < degdif; i++) {
                // substract from coefficient at index i + degdif the div * coefficient of q
                List<Rational> subCoefficients = mulList(difference, q.coefficients[i]);
                List<Rational> mulhighcoeff = mulList(extendcoeff.get(i), highestCoeffq);
                extendcoeff.set(i, minusList(mulhighcoeff, subCoefficients));
                extendcoeff.remove(degdif);
            }
            // Update sizes
            degp -= 1;
            degdif -= 1;
        }
        return extendcoeff;
    }
    */

    public Rational [] mulConst(Rational [] coeff, Rational cons) {
        Rational [] result = new Rational[coeff.length];
        for (int i = 0; i < coeff.length; i++) {
            result[i] = coeff[i].mul(cons);
        }
        return result;
    }

    public Rational [] mulList(Rational [] list1, Rational [] list2) {
        Rational [] result = new Rational[list1.length + list2.length - 1];
        for (int i = 0; i < list1.length+list2.length-1; i++) {
            result[i] = Rational.ZERO;
        }
        for (int i = 0; i < list1.length; i++) {
            for (int j = 0; j < list2.length; j++) {
                result[i+j] = result[i+j].add(list1[i].mul(list2[j]));
            }
        }
        return result;
    }

    public Rational [] minusList(Rational [] list1, Rational [] list2) {
        int max = list1.length;
        if (list2.length > list1.length) {
            max = list2.length;
        }
        Rational [] result = new Rational[max];
        for (int i = 0; i < list1.length; i++) {
            if (i < list2.length) {
                result[i] = list1[i].add(list2[i].negate());
            } else {
                result[i] = list1[i];
            }
        }
        if (list2.length > list1.length) {
            for (int i = 1; i <= list2.length-list1.length; i++) {
                result[list1.length + i - 1] = list2[i + list1.length - 1].negate();
            }
        }
        return result;
    }

    public int hashCode() {
        return coefficients.hashCode();
    }
}
