package org.scribble.del;

import org.scribble.ast.ScribNode;
import org.scribble.ast.RoleDecl;
import org.scribble.main.ScribbleException;
import org.scribble.sesstype.name.Role;
import org.scribble.visit.NameDisambiguator;
import org.scribble.visit.WellFormedChoiceChecker;
import org.scribble.visit.env.WellFormedChoiceEnv;

public class RoleDeclDel extends ScribDelBase
{
	@Override
	//public void enterBoundNamesCheck(ModelNode parent, ModelNode child, BoundNameChecker checker) throws ScribbleException
	public void enterDisambiguation(ScribNode parent, ScribNode child, NameDisambiguator disamb) throws ScribbleException
	{
		RoleDecl rd = (RoleDecl) child;
		disamb.addRole(rd.getDeclName());
	}

	@Override
	public RoleDecl leaveWFChoiceCheck(ScribNode parent, ScribNode child, WellFormedChoiceChecker checker, ScribNode visited) throws ScribbleException
	{
		WellFormedChoiceEnv env = checker.popEnv();
		RoleDecl rd = (RoleDecl) visited;
		Role role = rd.getDeclName();
		//Name dn = rd.getDeclarationName();
		/*if (env.isRoleBound(role))  // TODO: do for basic name checking (not WF choice)
		{
			throw new ScribbleException("Duplicate role delcaration: " + role);
		}*/

		//env.roles.enableRole(Role.EMPTY_ROLE, dn, RolesEnv.DEFAULT_ENABLING_OP);
		env = env.enableRoleForRootProtocolDecl(role);
		checker.pushEnv(env);
		//return rd;

		return (RoleDecl) super.leaveWFChoiceCheck(parent, child, checker, rd);
	}
}
