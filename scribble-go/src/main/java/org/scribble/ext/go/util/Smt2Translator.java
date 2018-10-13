package org.scribble.ext.go.util;

import java.util.Set;
import java.util.stream.Collectors;

import org.scribble.ext.go.type.index.RPIndexVar;

public abstract class Smt2Translator
{
	/*enum Sort { Int, Pair }
	
	private final Sort sort;*/
	
	public Smt2Translator()
	{
		//this.sort = sort;
	}
	
	public abstract String getSort();
	public abstract String getLtOp();
	public abstract String getLteOp();
	public abstract String getGtOp();
	public abstract String getGteOp();
	
	public String makeVarDecl(RPIndexVar v)
	{
		return "(" + v.toSmt2Formula() + " " + getSort() + ")";  // Factor out
	}

	public String makeExists(Set<RPIndexVar> vars, String body)
	{
		return "(exists "
				+ "(" + vars.stream().map(x -> makeVarDecl(x)).collect(Collectors.joining(" ")) + ")"
				+ body + ")";
	}

	public String makeForall(Set<RPIndexVar> vars, String body)
	{
		// TODO: factor out with above
		return "(forall "
				+ "(" + vars.stream().map(x -> makeVarDecl(x)).collect(Collectors.joining(" ")) + ")"
				+ body + ")";
	}

	public String makeLt(String x, String y)
	{
		return "(" + getLtOp() + " " + x + " " + y + ")"; 
	}

	public String makeLte(String x, String y)
	{
		return "(" + getLteOp() + " " + x + " " + y + ")"; 
	}

	public String makeGt(String x, String y)
	{
		return "(" + getGtOp() + " " + x + " " + y + ")"; 
	}

	public String makeGte(String x, String y)
	{
		return "(" + getGteOp() + " " + x + " " + y + ")"; 
	}

	public String makeAnd(Set<String> cs)
	{
		return "(and " + cs.stream().collect(Collectors.joining(" ")) + ")"; 
	}

	public String makeOr(Set<String> cs)
	{
		return "(or " + cs.stream().collect(Collectors.joining(" ")) + ")"; 
	}

	public String makeNot(String c)
	{
		return "(not " + "(" + c + "))"; 
	}
}
