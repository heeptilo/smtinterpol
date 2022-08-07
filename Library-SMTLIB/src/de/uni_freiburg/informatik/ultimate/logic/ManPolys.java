/*
 * Copyright (C) 2022, Tilo Heep
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

public class ManPolys {
    
   /** Function to perform a longdivision given a polynomial q and polynomial p
    * @param p nominator polynomial
    * @param q denomiantor polynomial
    * @return List of polynomial quotient and polynomial rest
     * Returns a List of polynomials (index 0 -> quotient, index 1 -> rest)
     */
    public static Polynomial [] longdivision(Polynomial p, Polynomial q) {
        p = p.removeZeros();
        q = q.removeZeros();
        int degp = p.getSize();
        int degq = q.getSize();
        int degdif = degp - degq;

        Polynomial [] result = new Polynomial[2];

        // Basis cases if p or q is zero
        if (degq > degp || degq == 0 || degp == 0) {
            Polynomial quotient = new Polynomial();
            result[0] = quotient;
            result[1] = p;
            return result;
        }
        // Initialize rest as p
        // Initialize quotient as an emty list
        Rational [] restcoefficients = new Rational[degp];
        Rational [] quotientcoeffitients = new Rational[degdif + 1];
        // output Polynomials
        Polynomial quotient = new Polynomial(quotientcoeffitients);
        Polynomial rest = new Polynomial(restcoefficients);
        // copy p into the rest
        for (int i = 0; i < degp; i++) {
            restcoefficients[i] = p.coefficients[i];
        }

        int size = degdif;

        while (degp >= degq) {
            // leading coefficients (of q not zero)
            Rational div = restcoefficients[degp - 1].div(q.coefficients[degq - 1]);

            // from lowest possible coefficient in p such that q * div 
            // has the same exponent iterate to the end
            quotientcoeffitients[size - degdif] = div;
            for ( int i = 0; i < degq; i++) {
                // substract from coefficient at index i + degdif the div * coefficient of q
                restcoefficients[i + degdif] = restcoefficients[i + degdif].sub(div.mul(q.coefficients[i]));
            }
            // Update sizes
            degp -= 1;
            degdif -= 1;
        }
        quotient = quotient.reverse();
        rest = rest.removeZeros();
        result[0] = quotient;
        result[1] = rest;
        return result;
    }

    public static BivariatePolynomial divideBiPoly(BivariatePolynomial p, BivariatePolynomial q) {
        // multiply coefficients with highest coefficient of q
        Rational [][] extendcoeff = p.coefficients;
        // save the highest coefficient (will always be multiplied with restcoefficients)
        Rational [] highestCoeffq = q.coefficients[q.getDegree()];
        int degdif = p.getSizeOverY() - q.getSizeOverY();

        int degp = p.getDegree();
        int degq = q.getDegree();

        while (degp >= degq) {
            // leading coefficient of p
            Rational [] highestCoeffp = extendcoeff[degp];

            // test if its possible to divide the leading coefficients
            Polynomial leadPolyp = new Polynomial(highestCoeffp);
            Polynomial leadPolyq = new Polynomial(highestCoeffq);
            Polynomial [] division = longdivision(leadPolyp, leadPolyq);
            if (division[1].coefficients.length == 0) {
                Polynomial quotient = division[0];
                highestCoeffp = quotient.coefficients;
            } else {
                // if the leading coefficient is not divisible all coefficients (except highest)
                // have to be extended by
                // the leading coefficient of q
                for (int i = 0; i < degp; i++) {
                    extendcoeff[i] = mulList(extendcoeff[i], highestCoeffq);
                }
            }
            for (int i = 0; i < degq; i++) {
                // substract from coefficient at index i + degdif the div * coefficient of q
                Rational [] subCoefficients = mulList(highestCoeffp, q.coefficients[i]);
                Rational [] mulhighcoeff = extendcoeff[i + degdif];
                extendcoeff[i + degdif] = minusList(mulhighcoeff, subCoefficients);
            }
            // delete extendcoeff[degp]
            // Update sizes
            degp -= 1;
            degdif -= 1;
        }
        //int restsize = extendcoeff.length - del;
        int restsize = degq;
        Rational [][] resultList = new Rational[restsize][];
        for (int i = 0; i < restsize; i++) {
            resultList[i] = extendcoeff[i];
        }
        BivariatePolynomial r = new BivariatePolynomial(resultList);
        return r;
    }

    /*
    public static BivariatePolynomial divideBiPolyold(BivariatePolynomial p, BivariatePolynomial q) {
        // multiply coefficients with highest coefficient of q
        List<List<Rational>> extendcoeff = p.getCoefficients();
        System.out.println(extendcoeff);
        System.out.println(q.coefficients);
        // save the highest coefficient (will always be multiplied with restcoefficients)
        List<Rational> highestCoeffq = q.coefficients.get(q.getDegree());
        int degdif = p.getSize() - q.getSize();

        int degp = p.getDegree();
        int degq = q.getDegree();

        while (degp >= degq) {
            // leading coefficient of p
            List<Rational> highestCoeffp = extendcoeff.get(extendcoeff.size() - 1);

            // test if its possible to divide the leading coefficients
            Polynomial leadPolyp = new Polynomial(highestCoeffp);
            Polynomial leadPolyq = new Polynomial(highestCoeffq);
            List<Polynomial> division = longdivision(leadPolyp, leadPolyq);
            if (division.get(1).coefficients.length == 0) {
                Polynomial quotient = division.get(0);
                highestCoeffp = quotient.coefficients;

            } else {
                // if the leading coefficient is not divisible all coefficients (except highest)
                // have to be extended by
                // the leading coefficient of q
                for (int i = 0; i < extendcoeff.size() - 1; i++) {
                    extendcoeff.set(i, mulList(extendcoeff.get(i), highestCoeffq));
                }
            }
            for (int i = 0; i < degq; i++) {
                // substract from coefficient at index i + degdif the div * coefficient of q
                List<Rational> subCoefficients = mulList(highestCoeffp, q.coefficients.get(i));
                List<Rational> mulhighcoeff = extendcoeff.get(i + degdif);
                extendcoeff.set(i + degdif, minusList(mulhighcoeff, subCoefficients));
            }
            extendcoeff.remove(degp);
            // Update sizes
            degp -= 1;
            degdif -= 1;
        }
        BivariatePolynomial r = new BivariatePolynomial(extendcoeff);
        return r;
    }

    public static List<Rational> mulConst(List<Rational> coeff, Rational cons) {
        List<Rational> result = new ArrayList<>();
        for (int i = 0; i < coeff.size(); i++) {
            result.add(coeff[i].mul(cons));
        }
        return result;
    }
    */


    public static Rational [] mulList(Rational [] list1, Rational [] list2) {
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

    public static Rational [] minusList(Rational [] list1, Rational [] list2) {
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
                result[list1.length + i - 1] = list2[list1.length + i - 1].negate();
            }
        }
        return result;
    }


    /**
     * Function that calculates the greatest common divisior of two polynomials p and q
     * if result is constant it returns an empty polynomial
     * @param p Polynomial with higher highest exponent
     * @param q Polynomial with lower highest exponent
     * @return Polynomial gcd(p,q)
     */
    public static Polynomial gcd(Polynomial p, Polynomial q) {
        Polynomial a = new Polynomial();
        Polynomial b = new Polynomial();
        Polynomial rest = new Polynomial();
        a = p;
        b = q;

        while (true) {
            rest = longdivision(a, b)[1];
            if (rest.getSize() >= b.getSize()) {
                a = rest;
            } else {
                a = b;
                b = rest;
                if (b.getSize() == 1) {
                    return new Polynomial();
                }
                if (b.getSize() == 0) {
                    return a;
                }
            }
        }
    }

    /**
     * Function that calculates the addition of two polynomials p and q
     * @param p Polynomial
     * @param q Polynomial
     * @return Polynomial p+q
     */
    public static Polynomial addPolynomials(Polynomial p, Polynomial q) {
        boolean pisbigger = false;

        if (q.getSize() == 0) {
            return p;
        }
        if (p.getSize() == 0) {
            return q;
        }

        int mindeg = 0;
        int maxdeg = 0;
        if (p.getDegree() > q.getDegree()) {
            mindeg = q.getDegree();
            maxdeg = p.getDegree();
            pisbigger = true;
        } else {
            mindeg = p.getDegree();
            maxdeg = q.getDegree();
            pisbigger = false;
        }
        Rational [] list1 = new Rational[maxdeg + 1];
        
        for (int i = 0; i <= mindeg; i++) {
            list1[i] = p.coefficients[i].add(q.coefficients[i]);
        }
        
        // if they have the same length we are finished
        if (p.getDegree() == q.getDegree()) {
            Polynomial a = new Polynomial(list1);
            return a;
        }
        
        for (int i = mindeg + 1; i <= maxdeg; i++) {
            if (pisbigger) {
                list1[i] = (p.coefficients[i]);
            } else {
                list1[i] = (q.coefficients[i]);
            }
        }
        Polynomial a = new Polynomial(list1);
        return a;
    }


    /**
     * Function that calculates product of two polynomials p and q if q is a linear factor
     * @param p Polynomial
     * @param q linear Polynomial
     * @return Polynomial p*q
     */
    public static Polynomial multiplyLinear(Polynomial p, Polynomial q) {

        Rational [] list1 = new Rational[p.getSize() + 1];
        Rational [] list2 = new Rational[p.getSize()];

        if (p.getSize() == 0) {
            return q;
        }
        if (q.getSize() == 0) {
            return p;
        }

        // add Zero to multiply the polynomial by x
        list1[0] = Rational.ZERO;
        for (int i = 0; i < p.getSize(); i++) {
            // multiply by coefficient of x in q
            list1[i + 1] = p.coefficients[i].mul(q.coefficients[1]);
        }

        for (int i = 0; i < p.getSize(); i++) {
            // multiply original polynomial p by the constant term of q
            list2[i] = (p.coefficients[i].mul(q.coefficients[0]));
        }

        Polynomial a = new Polynomial(list1);
        Polynomial b = new Polynomial(list2);

        return addPolynomials(a, b);
    }
}
