//! Project-authored registry of IR families, typed subsets and semantic models.
use super::*;
use serde::Deserialize;

table! {
    IrFamily = "ir_families", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        title: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    IrSyntaxKind = "ir_syntax_kinds", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        title: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    IrSubset = "ir_subsets", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        family: String = "TEXT NOT NULL",
        syntax_kind: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        title: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

/// The author's reading of the semantic declaration.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IrSemantics {
    #[default]
    Operational,
    Denotational,
}

impl Col for IrSemantics {
    fn sql(&self) -> Sql {
        Sql::Text(
            match self {
                Self::Operational => "operational",
                Self::Denotational => "denotational",
            }
            .into(),
        )
    }
}

table! {
    IrModel = "ir_models", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        subset: String = "TEXT NOT NULL",
        semantics: IrSemantics = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        institution: Option<String> = "TEXT",
        title: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}
