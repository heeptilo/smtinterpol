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
package de.uni_freiburg.informatik.ultimate.AlgebraicNumbersPackage;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
This class represents polynomials.
A polynomial is defined by its coefficients, a List of Rationals where
the coefficient of x**i has index i.
 *
 * @author Tilo Heep
 */
public class BivariatePolynomial {
    /**
	 * The list of coefficients of the polynomial 
	 */
    Rational [][] coefficients;

    /**
     * constructor with 2d array of Rationals as coefficients
     * @param coeff
     */
    public BivariatePolynomial(Rational [][] coeff) {
        coefficients = coeff;
    }

    public int getSizeOverY() {
        return coefficients.length;
    }

    public int getSizeOverX() {
        if (coefficients.length != 0) {
            return coefficients[0].length;
        } else {
            return 0;
        }
    }

    public int getDegree() {
        return coefficients.length - 1;
    }

    /**
     * creates a bivariate polynomial p(x-y)
     * where the polynomial of x is coefficient of the polynomial of y
     * @param p given Polynomial of which p(x-y) should be created
     * @returns Bivariate Polynomial p(x-y)
     */
    public static BivariatePolynomial subxy(Polynomial p) {
        Rational [][] resultcoefficients = new Rational[p.getSize()][];
        resultcoefficients[0] = p.coefficients;
        List<List<Integer>> binomlist = new ArrayList<>();
        binomlist = pascaltriangle(p.getDegree() + 1);
        for (int cg = 1; cg <= p.getDegree(); cg++) {
            // cg current degree of y
            Rational [] coeff = new Rational [p.getSize() - cg];
            for (int j = cg; j <= p.getDegree(); j++) {
                Rational c = p.coefficients[j];
                Rational co = c.mul(Rational.valueOf(binomlist.get(j).get(cg), 1));
                if (cg % 2 == 1) {
                    co = co.negate();
                }
                coeff[j - cg] = co;
            }

            resultcoefficients[cg] = coeff;
        }
        return new BivariatePolynomial(resultcoefficients);
    }

    /**
     * creates a bivariate polynomial p(x*y)
     * where the polynomial of x is coefficient of the polynomial of y
     * @param p given Polynomial of which p(x*y) should be created
     */
    public static BivariatePolynomial mulxy(Polynomial p) {
        Rational [][] resultcoefficients = new Rational[p.getSize()][];
        for (int i = 0; i <= p.getDegree(); i++) {
            // i current degree of y
            if (p.coefficients[i] != Rational.ZERO) {
                Rational [] coeff = new Rational[i + 1];
                for (int j = 0; j < i; j++) {
                    coeff[j] = Rational.ZERO;
                }
                coeff[i] = p.coefficients[i];
                resultcoefficients[i] = coeff;
            } else {
                Rational [] singlelist = new Rational[1];
                singlelist[0] = Rational.ZERO;
                resultcoefficients[i] = singlelist;
            }
        }
        return new BivariatePolynomial(resultcoefficients);
    }

    private static List<Integer> newPascalrow(List<Integer> binomlist) {
        List<Integer> newPascallist = new ArrayList<>();
        newPascallist.add(1);
        if (binomlist.size() == 0) {
            return newPascallist;
        }
        for (int i = 0; i < binomlist.size() - 1; i++) {
            newPascallist.add(binomlist.get(i) + binomlist.get(i+1));
        }
        newPascallist.add(1);
        return newPascallist;
    }

    /**
     * Builds a pascaltriangle of depth size
     * @param size
     * @return pascaltriangle of a list of list of ints
     */
    public static List<List<Integer>> pascaltriangle(int size) {
        List<List<Integer>> triangle = new ArrayList<>();
        List<Integer> pascalrow = new ArrayList<>();
        for (int i = 0; i < size; i++) {
            pascalrow = newPascalrow(pascalrow);
            triangle.add(pascalrow);
        }
        return triangle;
    }


    /** Function that orders the coefficients in the reverse order
     */
    private BivariatePolynomial reverse() {
        Rational result [][] = new Rational[getSizeOverY()][getSizeOverX()];
        if (getSizeOverY() == 0) {
            BivariatePolynomial res = new BivariatePolynomial(result);
            return res;
        }
        int m = getSizeOverY();
        for (int i = 1; i < m + 1; i++ ) {
            result[i - 1] = coefficients[m-i];
        }
        BivariatePolynomial res = new BivariatePolynomial(result);
        return res;
    }

    /** 
     * Funktion that removes the zeros if there are any at the position of the highest exponents
    */
    public BivariatePolynomial removeZeros() {
        Rational [][] coeff = new Rational[getSizeOverY()][coefficients[0].length];
        if (getSizeOverY() == 0) {
            return new BivariatePolynomial(coefficients);
        }
        for (int i = 0; i < getSizeOverY(); i++) {
            coeff[i] =  coefficients[getSizeOverY() - i - 1];
        }
        int size = coeff.length;
        int removes = 0;
        int iter = 0;
        while (size != 0) {
            if (isZero(coeff[iter])) {
                removes++;
                size--;
            } else {
                break;
            }
            iter++;
        }
        Rational [][] coeffs = new Rational[size][coefficients[0].length];
        for (int i = 0; i < size; i++) {
            coeffs[i] = coeff[i + removes];
        }
        BivariatePolynomial result = new BivariatePolynomial(coeffs);
        result = result.reverse();
        return result;
    }

    private Boolean isZero(Rational[] list) {
        for (int i = 0; i < list.length; i++) {
            if (list[i] != Rational.ZERO) {
                return false;
            }
        }
        return true;
    }

    /*
    private List<Rational> divideConst(List<Rational> coeff, Rational constant) {
        List<Rational> result = new ArrayList<>();
        for (int i = 0; i < coeff.size(); i++) {
            result.add(coeff.get(i).div(constant));
        }
        return result;
    }

    private List<Rational> mulConst(List<Rational> coeff, Rational constant) {
        List<Rational> result = new ArrayList<>();
        for (int i = 0; i < coeff.size(); i++) {
            result.add(coeff.get(i).mul(constant));
        }
        return result;
    }
    
    private List<Rational> subPoly(List<Rational> l1, List<Rational> l2) {
        List<Rational> result = new ArrayList<>();
        for (int i = 0; i < l1.size(); i++) {
            if (i < l2.size()) {
                result.add(l1.get(i).sub(l2.get(i)));
            } else {
                result.add(l1.get(i));
            }
        }
        return result;
    }
    */
}