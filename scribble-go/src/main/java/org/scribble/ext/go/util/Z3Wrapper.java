package org.scribble.ext.go.util;

import java.io.File;
import java.util.Arrays;

import org.scribble.ast.ProtocolDecl;
import org.scribble.ext.go.main.GoJob;
import org.scribble.ext.go.type.index.RPIndexExpr;
import org.scribble.ext.go.type.index.RPIndexPair;
import org.scribble.main.ScribbleException;
import org.scribble.type.kind.Global;
import org.scribble.util.ScribUtil;

// "Native" Z3 -- not Z3 Java API
public class Z3Wrapper
{

	/*public static String getSmt2VarDecl(RPIndexExpr x)
	{
		if (x instanceof RPIndexPair)
		{
			return ()
		}
	}*/

	/*public static String getSmt2_lte(RPIndexExpr x, RPIndexExpr y)
	{
		String op;
		if (x instanceof RPIndexPair)
		{
			if (!(y instanceof RPIndexPair))
			{
				throw new RuntimeException("Shouldn't get in here: " + x + ", " + y);
			}
			op = "pair_lte";
		}
		else
		{
			op = "<=";
		}
		return "(" + op + " " + x.toSmt2Formula() + " " + y.toSmt2Formula() + ")";
	}

	public static String getSmt2_lt(RPIndexExpr x, RPIndexExpr y)
	{
		String op;
		if (x instanceof RPIndexPair)
		{
			if (!(y instanceof RPIndexPair))
			{
				throw new RuntimeException("Shouldn't get in here: " + x + ", " + y);
			}
			op = "pair_lt";
		}
		else
		{
			op = "<";
		}
		return "(" + op + " " + x.toSmt2Formula() + " " + y.toSmt2Formula() + ")";
	}

	public static String getSmt2_gte(RPIndexExpr x, RPIndexExpr y)
	{
		String op;
		if (x instanceof RPIndexPair)
		{
			if (!(y instanceof RPIndexPair))
			{
				throw new RuntimeException("Shouldn't get in here: " + x + ", " + y);
			}
			op = "pair_gte";
		}
		else
		{
			op = ">=";
		}
		return "(" + op + " " + x.toSmt2Formula() + " " + y.toSmt2Formula() + ")";
	}

	public static String getSmt2_gt(RPIndexExpr x, RPIndexExpr y)
	{
		String op;
		if (x instanceof RPIndexPair)
		{
			if (!(y instanceof RPIndexPair))
			{
				throw new RuntimeException("Shouldn't get in here: " + x + ", " + y);
			}
			op = "pair_gt";
		}
		else
		{
			op = ">";
		}
		return "(" + op + " " + x.toSmt2Formula() + " " + y.toSmt2Formula() + ")";
	}*/

	// Based on CommandLine::runDot, JobContext::runAut, etc
	public static boolean checkSat(GoJob job, ProtocolDecl<Global> gpd, String smt2) //throws ScribbleException
	{
		String tmpName = gpd.header.name + ".smt2.tmp";
		File tmp = new File(tmpName);
		if (tmp.exists())  // Factor out with CommandLine.runDot (file exists check)
		{
			throw new RuntimeException("Cannot overwrite: " + tmpName);
		}
		smt2 = "(declare-datatypes (T1 T2) ((Pair (mk-pair (fst T1) (snd T2)))))\n"
			+ "(define-fun pair_max ((p!1 (Pair Int Int))) Int (ite (< (fst p!1) (snd p!1)) (snd p!1) (fst p!1) ) )\n"
			+	"(define-fun pair_min ((p!1 (Pair Int Int))) Int (ite (< (fst p!1) (snd p!1)) (fst p!1) (snd p!1)))\n"
			+	"(define-fun twopair_max ((p!1 (Pair Int Int)) (p!2 (Pair Int Int))) Int (ite (< (pair_max p!1) (pair_max p!2)) (pair_max p!2) (pair_max p!1)))\n"
			+ "(define-fun twopair_min ((p!1 (Pair Int Int)) (p!2 (Pair Int Int))) Int (ite (< (pair_min p!1) (pair_min p!2)) (pair_min p!1) (pair_min p!2)))\n"
			+ "(define-fun pair_lte ((p!1 (Pair Int Int)) (p!2 (Pair Int Int))) Bool (and (<= (fst p!1) (fst p!2)) (<= (snd p!1) (snd p!2)) ))\n"
			+ "(define-fun pair_lt ((p!1 (Pair Int Int)) (p!2 (Pair Int Int))) Bool (and (pair_lte p!1 p!2) (not (= p!1 p!2))))\n"
			+ "(define-fun pair_gte ((p!1 (Pair Int Int)) (p!2 (Pair Int Int))) Bool (pair_lte p!2 p!1))\n"
			+ "(define-fun pair_gt ((p!1 (Pair Int Int)) (p!2 (Pair Int Int))) Bool (pair_lt p!2 p!1))\n"
			+ smt2;
		smt2 = smt2 + "\n(check-sat)\n(exit)";
		try
		{
			ScribUtil.writeToFile(tmpName, smt2);
			String[] res = ScribUtil.runProcess("z3", tmpName);
			String trim = res[0].trim();
			if (trim.equals("sat"))  // FIXME: factor out
			{
				return true;
			}
			else if (trim.equals("unsat"))
			{
				return false;
			}
			else
			{
				throw new RuntimeException("[assrt] Z3 error: " + Arrays.toString(res));
			}
		}
		catch (ScribbleException e)
		{
			throw new RuntimeException(e);
		}
		finally
		{
			tmp.delete();
		}
	}
}
