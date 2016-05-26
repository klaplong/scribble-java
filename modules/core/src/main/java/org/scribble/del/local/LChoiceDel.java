package org.scribble.del.local;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.scribble.ast.AstFactoryImpl;
import org.scribble.ast.ScribNode;
import org.scribble.ast.local.LChoice;
import org.scribble.ast.local.LProtocolBlock;
import org.scribble.ast.name.simple.RoleNode;
import org.scribble.del.ChoiceDel;
import org.scribble.main.ScribbleException;
import org.scribble.sesstype.kind.RoleKind;
import org.scribble.sesstype.name.RecVar;
import org.scribble.sesstype.name.Role;
import org.scribble.visit.EndpointGraphBuilder;
import org.scribble.visit.ProjectedChoiceSubjectFixer;
import org.scribble.visit.ProjectedSubprotocolPruner;
import org.scribble.visit.ProtocolDefInliner;
import org.scribble.visit.ReachabilityChecker;
import org.scribble.visit.env.InlineProtocolEnv;
import org.scribble.visit.env.ReachabilityEnv;

public class LChoiceDel extends ChoiceDel implements LCompoundInteractionNodeDel
{
	@Override
	public ScribNode leaveProjectedChoiceSubjectFixing(ScribNode parent, ScribNode child, ProjectedChoiceSubjectFixer fixer, ScribNode visited) throws ScribbleException
	{
		LChoice lc = (LChoice) visited;
		List<LProtocolBlock> blocks = lc.getBlocks();
		
		Set<Role> subjs = blocks.stream()
				.map((b) -> b.getInteractionSeq().getInteractions().get(0).inferLocalChoiceSubject(fixer))
				//.filter((r) -> !r.toString().equals(DummyProjectionRoleNode.DUMMY_PROJECTION_ROLE))
				.collect(Collectors.toSet());
		if (subjs.size() == 0)
		{
			//throw new RuntimeScribbleException("TODO: unable to infer projection subject: " + parent);
			throw new RuntimeException("Shouldn't get in here: " + subjs);  // FIXME: should be OK now by model-based WF
		}
		else
		{
			subjs = subjs.stream()
					.map((r) -> fixer.isRecVarRole(r) ? fixer.getChoiceSubject(new RecVar(r.toString())) : r)  // Never needed?
					.collect(Collectors.toSet());
		}
		
		// HACK?  (for non- role-balanced choice cases)
		subjs = subjs.stream().filter((s) -> s != null).collect(Collectors.toSet());
		
		if (subjs.size() > 1)  // Unnecessary: due to WF check in GChoiceDel.leaveInlinedPathCollection -- would be better as a check on locals than in projection anyway
		{
			//throw new ScribbleException("Inconsistent projected choice subject: " + subjs);
			throw new RuntimeException("Shouldn't get in here: " + subjs);
		}
		RoleNode subj = (RoleNode) AstFactoryImpl.FACTORY.SimpleNameNode(RoleKind.KIND,
				//blocks.get(0).getInteractionSeq().getInteractions().get(0).inferLocalChoiceSubject(fixer).toString());
				subjs.iterator().next().toString());
		fixer.setChoiceSubject(subj.toName());
		LChoice projection = AstFactoryImpl.FACTORY.LChoice(subj, blocks);
		return projection;
	}

	@Override
	public ScribNode leaveProtocolInlining(ScribNode parent, ScribNode child, ProtocolDefInliner inl, ScribNode visited) throws ScribbleException
	{
		LChoice lc = (LChoice) visited;
		List<LProtocolBlock> blocks = 
				lc.getBlocks().stream().map((b) -> (LProtocolBlock) ((InlineProtocolEnv) b.del().env()).getTranslation()).collect(Collectors.toList());	
		RoleNode subj = lc.subj.clone();
		LChoice inlined = AstFactoryImpl.FACTORY.LChoice(subj, blocks);
		inl.pushEnv(inl.popEnv().setTranslation(inlined));
		return (LChoice) super.leaveProtocolInlining(parent, child, inl, lc);
	}

	@Override
	public LChoice leaveReachabilityCheck(ScribNode parent, ScribNode child, ReachabilityChecker checker, ScribNode visited) throws ScribbleException
	{
		LChoice cho = (LChoice) visited;
		List<ReachabilityEnv> benvs =
				cho.getBlocks().stream().map((b) -> (ReachabilityEnv) b.del().env()).collect(Collectors.toList());
		ReachabilityEnv merged = checker.popEnv().mergeForChoice(benvs);
		checker.pushEnv(merged);
		return (LChoice) LCompoundInteractionNodeDel.super.leaveReachabilityCheck(parent, child, checker, visited);  // records the current checker Env to the current del; also pops and merges that env into the parent env
	}

	public LChoice visitForFsmConversion(EndpointGraphBuilder graph, LChoice child)
	{
		try
		{
			graph.builder.enterChoice();  // FIXME: refactor enter/leave properly

			for (LProtocolBlock block : child.getBlocks())
			{
				graph.builder.pushChoiceBlock();
				block.accept(graph);
				graph.builder.popChoiceBlock();
			}
			
			graph.builder.leaveChoice();
		}
		catch (ScribbleException e)
		{
			throw new RuntimeException("Shouldn't get in here: " + e);
		}
		return child;
	}

	@Override
	public ScribNode leaveProjectedSubprotocolPruning(ScribNode parent, ScribNode child, ProjectedSubprotocolPruner pruner, ScribNode visited) throws ScribbleException
	{
		LChoice lc = (LChoice) visited;
		List<LProtocolBlock> blocks = lc.getBlocks().stream().filter((b) -> !b.isEmpty()).collect(Collectors.toList());
		if (blocks.isEmpty())
		{
			return null;
		}
		return lc.reconstruct(lc.subj, blocks);
	}
}
