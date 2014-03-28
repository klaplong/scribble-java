/*
 * Copyright 2009-11 www.scribble.org
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */
package org.scribble.context;

import org.scribble.model.Module;

/**
 * This class provides a cache for parsed modules.
 *
 */
public class ModuleCache {

	private java.util.Map<String,Module> _modules=new java.util.HashMap<String,Module>();
	
	/**
	 * This method registers the supplied module with the cache.
	 * 
	 * @param module The module
	 */
	public void register(Module module) {
		_modules.put(module.getName().toString(), module);
	}
	
	/**
	 * This method returns the module associated with the
	 * supplied name.
	 * 
	 * @param name The name
	 * @return The module, or null if not found
	 */
	public Module getModule(String name) {
		return (_modules.get(name));
	}
}