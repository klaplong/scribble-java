/*
 * Copyright 2009-11 www.scribble.org
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
package org.scribble.protocol.conformance;

import org.scribble.common.logging.Journal;
import org.scribble.protocol.model.ModelObject;

/**
 * This implementation records conformance related information to the logging journal.
 * 
 * WARNING: This component is still in the EXPERIMENTAL stage, so its API could change.
 */
public class LoggingConformanceHandler implements ConformanceHandler {

    //private Journal m_logger=null;
    
    /**
     * Conformance model object.
     */
    public static final String CONFORMANCE_MODEL_OBJECT="Conformance.Model.Object";

    /**
     * Conformance model object.
     */
    public static final String CONFORMANCE_REFERENCE_PARENT="Conformance.Reference.Parent";
    
    /**
     * Conformance model object.
     */
    public static final String CONFORMANCE_REFERENCE_INDEX="Conformance.Reference.Index";
    
    /**
     * Conformance model object.
     */
    public static final String CONFORMANCE_REFERENCE_OBJECT="Conformance.Reference.Object";
    
    /**
     * This constructor initialises the conformance handler with the journal.
     * 
     * @param logger The journal
     */
    public LoggingConformanceHandler(Journal logger) {
        //m_logger = logger;
    }

    /**
     * This method indicates that a new model object has been detected in
     * the model. The position of the new object, relative to the reference
     * model, is provided by the parent model object in the reference model
     * and optionally the index (where relevant).
     * 
     * @param modelObject The new model object, from the model being checked
     * @param refParent The 'parent' model object, from the reference model,
     *                         that would contain the new object
     * @param index The child index, in the reference model, where the new
     *                     model object would be positioned
     */
    public void added(ModelObject modelObject, ModelObject refParent, int index) {    
    }

    /**
     * This method indicates that a change has been detected between
     * equivalent model objects found in the primary and reference models.
     * 
     * @param modelObject The model object, from the model being checked
     * @param refObject The model object, from the reference model
     */
    public void updated(ModelObject modelObject, ModelObject refObject) {
    }

    /**
     * This method indicates that a model object within the reference model
     * does not exist in the model being conformance checked.
     * 
     * @param refObject The model object, not found in the primary model,
     *                         as defined in the reference model
     */
    public void removed(ModelObject refObject) {
    }
    
}