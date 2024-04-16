use std::{collections::HashMap, fmt::Debug, sync::Arc};

/// Represents an attribute of a thing in the Thingverse.
///
/// An attribute consists of a name and a value. The name is a string that uniquely identifies
/// the attribute within a thing. The value is of type `Value`, which can be either `Quantitative`
/// or `Categorical`.
///
/// # Examples
///
/// ```
/// use thingverse::{Attribute, Value, Quantitative};
///
/// let attribute = Attribute {
///     name: "height".to_string(),
///     value: Value::Quantitative(Quantitative {
///         value: Some(180.5),
///         unit: "cm".to_string(),
///         precision: 1,
///         value_type: "length".to_string(),
///         display_format: "{:.1} cm".to_string(),
///     }),
/// };
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Attribute {
    name: String,
    value: Value,
}

/// Represents the value associated with an attribute.
///
/// The `Value` enum has two variants: `Quantitative` and `Categorical`. `Quantitative` represents
/// a continuous or measurable value, while `Categorical` represents a discrete or categorical value.
///
/// # Examples
///
/// ```
/// use thingverse::{Value, Quantitative, Categorical};
///
/// let quantitative_value = Value::Quantitative(Quantitative {
///     value: Some(42.0),
///     unit: "kg".to_string(),
///     precision: 2,
///     value_type: "weight".to_string(),
///     display_format: "{:.2} kg".to_string(),
/// });
///
/// let categorical_value = Value::Categorical(Categorical {
///     value: Some("red".to_string()),
///     value_type: "color".to_string(),
/// });
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Quantitative(Quantitative),
    Categorical(Categorical),
}

/// Represents a quantitative or continuous value.
///
/// A `Quantitative` value has the following properties:
///
/// - `value`: An optional `f64` representing the numeric value. It is wrapped in an `Option` to handle unknown values.
/// - `unit`: A string representing the unit of measurement for the value.
/// - `precision`: An unsigned 32-bit integer representing the number of decimal places for the value.
/// - `value_type`: A string describing the type or category of the value.
/// - `display_format`: A string specifying the format for displaying the value.
///
/// # Examples
///
/// ```
/// use thingverse::Quantitative;
///
/// let quantitative = Quantitative {
///     value: Some(3.14159),
///     unit: "rad".to_string(),
///     precision: 5,
///     value_type: "angle".to_string(),
///     display_format: "{:.5} rad".to_string(),
/// };
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Quantitative {
    value: Option<f64>,
    unit: String,
    precision: u32,
    value_type: String,
    display_format: String,
}

impl Eq for Quantitative {}
impl std::hash::Hash for Quantitative {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self.value {
            Some(v) => v.to_bits().hash(state),
            None => 0u64.hash(state),
        }
        self.unit.hash(state);
        self.precision.hash(state);
        self.value_type.hash(state);
        self.display_format.hash(state);
    }
}

/// Represents a categorical or discrete value.
///
/// A `Categorical` value has the following properties:
///
/// - `value`: An optional string representing the categorical value. It is wrapped in an `Option` to handle unknown values.
/// - `value_type`: A string describing the type or category of the value.
///
/// # Examples
///
/// ```
/// use thingverse::Categorical;
///
/// let categorical = Categorical {
///     value: Some("apple".to_string()),
///     value_type: "fruit".to_string(),
/// };
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Categorical {
    value: Option<String>,
    value_type: String,
}

/// Represents a law in the Thingverse.
///
/// A `Law` defines a rule or constraint that things must follow to be accepted into a universe.
/// It has the following properties:
///
/// - `target_attribute`: A string specifying the name of the attribute to which the law applies.
/// - `condition`: A closure that takes a reference to a `Thing` and returns a boolean indicating whether the law applies to the thing.
/// - `derivation_fn`: A closure that takes a reference to a `Thing` and returns an optional `Value` derived based on the law.
/// - `error_message`: A string containing the error message to be returned if the law is violated.
///
/// # Examples
///
/// ```
/// use thingverse::{Law, Thing, Value, Quantitative};
///
/// let law = Law {
///     target_attribute: "age".to_string(),
///     condition: Box::new(|thing: &Thing| thing.get_attribute_value("age").is_some()),
///     derivation_fn: Box::new(|thing: &Thing| {
///         let age = thing.get_attribute_value("age").and_then(|value| match value {
///             Value::Quantitative(quant) => quant.value,
///             _ => None,
///         })?;
///         Some(Value::Quantitative(Quantitative {
///             value: Some(age),
///             unit: "years".to_string(),
///             precision: 0,
///             value_type: "age".to_string(),
///             display_format: "{:.0} years".to_string(),
///         }))
///     }),
///     error_message: "Age must be specified".to_string(),
/// };
/// ```
#[derive(Clone)]
pub struct Law {
    target_attribute: String,
    condition: Arc<dyn Fn(&Thing) -> bool>,
    derivation_fn:  Arc<dyn Fn(&Thing) -> Option<Value>>,
    error_message: String,
}

impl Debug for Law {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Law")
            .field("target_attribute", &self.target_attribute)
            .field("error_message", &self.error_message)
            .finish()
    }
}


/// Represents a thing in the Thingverse.
///
/// A `Thing` is an entity that possesses attributes. It is represented by a collection of `Attribute` instances
/// stored in a `HashMap`. The keys of the `HashMap` are the attribute names, and the values are the corresponding
/// `Attribute` instances.
///
/// # Examples
///
/// ```
/// use std::collections::HashMap;
/// use thingverse::{Thing, Attribute, Value, Categorical};
///
/// let mut attributes = HashMap::new();
/// attributes.insert("name".to_string(), Attribute {
///     name: "name".to_string(),
///     value: Value::Categorical(Categorical {
///         value: Some("Apple".to_string()),
///         value_type: "fruit".to_string(),
///     }),
/// });
///
/// let thing = Thing { attributes };
/// ```
#[derive(Debug, Clone)]
pub struct Thing {
    attributes: HashMap<String, Attribute>,
}

impl Thing {
    /// Creates a new `Thing` with empty attributes.
    ///
    /// # Examples
    ///
    /// ```
    /// use thingverse::Thing;
    ///
    /// let thing = Thing::new();
    /// ```
    pub fn new() -> Self {
        Thing {
            attributes: HashMap::new(),
        }
    }

    /// Adds an attribute to the `Thing`.
    ///
    /// If an attribute with the same name already exists, it will be overwritten.
    ///
    /// # Examples
    ///
    /// ```
    /// use thingverse::{Thing, Attribute, Value, Quantitative};
    ///
    /// let mut thing = Thing::new();
    /// let attribute = Attribute {
    ///     name: "weight".to_string(),
    ///     value: Value::Quantitative(Quantitative {
    ///         value: Some(500.0),
    ///         unit: "grams".to_string(),
    ///         precision: 1,
    ///         value_type: "weight".to_string(),
    ///         display_format: "{:.1} g".to_string(),
    ///     }),
    /// };
    /// thing.add_attribute(attribute);
    /// ```
    pub fn add_attribute(&mut self, attribute: Attribute) {
        self.attributes.insert(attribute.name.clone(), attribute);
    }

    /// Retrieves the value of an attribute by its name.
    ///
    /// Returns an `Option` containing a reference to the `Value` if the attribute exists,
    /// or `None` if the attribute is not found.
    ///
    /// # Examples
    ///
    /// ```
    /// use thingverse::{Thing, Attribute, Value, Categorical};
    ///
    /// let mut thing = Thing::new();
    /// let attribute = Attribute {
    ///     name: "color".to_string(),
    ///     value: Value::Categorical(Categorical {
    ///         value: Some("blue".to_string()),
    ///         value_type: "color".to_string(),
    ///     }),
    /// };
    /// thing.add_attribute(attribute);
    ///
    /// assert_eq!(thing.get_attribute_value("color"), Some(&Value::Categorical(Categorical {
    ///     value: Some("blue".to_string()),
    ///     value_type: "color".to_string(),
    /// })));
    /// assert_eq!(thing.get_attribute_value("size"), None);
    /// ```
    pub fn get_attribute_value(&self, name: &str) -> Option<&Value> {
        self.attributes.get(name).map(|attr| &attr.value)
    }

    /// Sets the value of an attribute by its name.
    ///
    /// If the attribute exists, its value will be updated. If the attribute does not exist,
    /// nothing will happen.
    ///
    /// # Examples
    ///
    /// ```
    /// use thingverse::{Thing, Attribute, Value, Quantitative};
    ///
    /// let mut thing = Thing::new();
    /// let attribute = Attribute {
    ///     name: "height".to_string(),
    ///     value: Value::Quantitative(Quantitative {
    ///         value: Some(150.0),
    ///         unit: "cm".to_string(),
    ///         precision: 1,
    ///         value_type: "height".to_string(),
    ///         display_format: "{:.1} cm".to_string(),
    ///     }),
    /// };
    /// thing.add_attribute(attribute);
    ///
    /// let new_value = Value::Quantitative(Quantitative {
    ///     value: Some(160.0),
    ///     unit: "cm".to_string(),
    ///     precision: 1,
    ///     value_type: "height".to_string(),
    ///     display_format: "{:.1} cm".to_string(),
    /// });
    /// thing.set_attribute_value("height", new_value);
    /// ```
    pub fn set_attribute_value(&mut self, name: &str, value: Value) {
        if let Some(attr) = self.attributes.get_mut(name) {
            attr.value = value;
        }
    }
}

/// Represents a universe in the Thingverse.
///
/// A `Universe` is a collection of `Thing` instances and a set of `Law` instances that govern the things in the universe.
/// It provides methods to add things, add laws, and review things against the laws to determine if they are accepted into the universe.
///
/// # Examples
///
/// ```
/// use thingverse::{Universe, Thing, Law, Value, Quantitative};
///
/// let mut universe = Universe::new();
///
/// // Add a law to the universe
/// let law = Law {
///     target_attribute: "age".to_string(),
///     condition: Box::new(|thing: &Thing| thing.get_attribute_value("age").is_some()),
///     derivation_fn: Box::new(|thing: &Thing| {
///         let age = thing.get_attribute_value("age").and_then(|value| match value {
///             Value::Quantitative(quant) => quant.value,
///             _ => None,
///         })?;
///         Some(Value::Quantitative(Quantitative {
///             value: Some(age),
///             unit: "years".to_string(),
///             precision: 0,
///             value_type: "age".to_string(),
///             display_format: "{:.0} years".to_string(),
///         }))
///     }),
///     error_message: "Age must be specified".to_string(),
/// };
/// universe.add_law(law);
///
/// // Create a thing
/// let mut thing = Thing::new();
/// thing.add_attribute(Attribute {
///     name: "age".to_string(),
///     value: Value::Quantitative(Quantitative {
///         value: Some(25.0),
///         unit: "years".to_string(),
///         precision: 0,
///         value_type: "age".to_string(),
///         display_format: "{:.0} years".to_string(),
///     }),
/// });
///
/// // Review the thing against the laws of the universe
/// let result = universe.review(&thing);
/// assert!(result.is_ok());
/// ```
#[derive(Debug, Clone)]
pub struct Universe {
    things: Vec<Thing>,
    laws: Vec<Law>,
}

impl Universe {
    /// Creates a new `Universe` with empty things and laws.
    ///
    /// # Examples
    ///
    /// ```
    /// use thingverse::Universe;
    ///
    /// let universe = Universe::new();
    /// ```
    pub fn new() -> Self {
        Universe {
            things: Vec::new(),
            laws: Vec::new(),
        }
    }

    /// Adds a `Thing` to the universe.
    ///
    /// # Examples
    ///
    /// ```
    /// use thingverse::{Universe, Thing};
    ///
    /// let mut universe = Universe::new();
    /// let thing = Thing::new();
    /// universe.add_thing(thing);
    /// ```
    pub fn add_thing(&mut self, thing: Thing) {
        self.things.push(thing);
    }

    /// Adds a `Law` to the universe.
    ///
    /// # Examples
    ///
    /// ```
    /// use thingverse::{Universe, Law, Thing, Value, Quantitative};
    ///
    /// let mut universe = Universe::new();
    ///
    /// let law = Law {
    ///     target_attribute: "age".to_string(),
    ///     condition: Box::new(|thing: &Thing| thing.get_attribute_value("age").is_some()),
    ///     derivation_fn: Box::new(|thing: &Thing| {
    ///         let age = thing.get_attribute_value("age").and_then(|value| match value {
    ///             Value::Quantitative(quant) => quant.value,
    ///             _ => None,
    ///         })?;
    ///         Some(Value::Quantitative(Quantitative {
    ///             value: Some(age),
    ///             unit: "years".to_string(),
    ///             precision: 0,
    ///             value_type: "age".to_string(),
    ///             display_format: "{:.0} years".to_string(),
    ///         }))
    ///     }),
    ///     error_message: "Age must be specified".to_string(),
    /// };
    ///
    /// universe.add_law(law);
    /// ```
    pub fn add_law(&mut self, law: Law) {
        self.laws.push(law);
    }

    /// Reviews a `Thing` against the laws of the universe to determine if it is accepted.
    ///
    /// Returns `Ok(())` if the thing is accepted, or `Err(String)` with an error message if the thing violates any of the laws.
    ///
    /// # Examples
    ///
    /// ```
    /// use thingverse::{Universe, Thing, Law, Value, Quantitative};

    /// let mut universe = Universe::new();
    ///
    /// // Add a law to the universe
    /// let law = Law {
    ///     target_attribute: "age".to_string(),
    ///     condition: Box::new(|thing: &Thing| thing.get_attribute_value("age").is_some()),
    ///     derivation_fn: Box::new(|thing: &Thing| {
    ///         let age = thing.get_attribute_value("age").and_then(|value| match value {
    ///             Value::Quantitative(quant) => quant.value,
    ///             _ => None,
    ///         })?;
    ///         Some(Value::Quantitative(Quantitative {
    ///             value: Some(age),
    ///             unit: "years".to_string(),
    ///             precision: 0,
    ///             value_type: "age".to_string(),
    ///             display_format: "{:.0} years".to_string(),
    ///         }))
    ///     }),
    ///     error_message: "Age must be specified".to_string(),
    /// };
    /// universe.add_law(law);
    ///
    /// // Create a thing
    /// let mut thing = Thing::new();
    /// thing.add_attribute(Attribute {
    ///     name: "age".to_string(),
    ///     value: Value::Quantitative(Quantitative {
    ///         value: Some(25.0),
    ///         unit: "years".to_string(),
    ///         precision: 0,
    ///         value_type: "age".to_string(),
    ///         display_format: "{:.0} years".to_string(),
    ///     }),
    /// });
    ///
    /// // Review the thing against the laws of the universe
    /// let result = universe.review(&thing);
    /// assert!(result.is_ok());
    ///
    /// // Create another thing that violates the law
    /// let mut invalid_thing = Thing::new();
    /// invalid_thing.add_attribute(Attribute {
    ///     name: "name".to_string(),
    ///     value: Value::Categorical(Categorical {
    ///         value: Some("John".to_string()),
    ///         value_type: "name".to_string(),
    ///     }),
    /// });
    ///
    /// // Review the invalid thing against the laws of the universe
    /// let result = universe.review(&invalid_thing);
    /// assert!(result.is_err());
    /// ```
    pub fn review(&self, thing: &Thing) -> Result<(), String> {
        for law in &self.laws {
            if (law.condition)(thing) {
                let derived_value = (law.derivation_fn)(thing);
                match derived_value {
                    Some(_) => (),
                    None => return Err(law.error_message.clone()),
                }
            }
        }
        Ok(())
    }
}

// Trait for converting a thing to a specific type.
pub trait IntoType<T> {
    fn into_type(&self) -> Option<T>;
}

// Trait for validating a thing.
pub trait Validate {
    fn validate(&self) -> Result<(), String>;
}
