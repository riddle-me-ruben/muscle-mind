import pymysql
from flask import current_app
from dotenv import load_dotenv
import os

"""
Description:
The DatabaseManager class is responsible for managing connections and executing SQL queries on the MySQL database.
It supports efficient handling of database operations, such as establishing connections, executing queries,
and committing changes. The class is implemented as a singleton to ensure only one instance is created and reused.

Semi-formal Notation:
/*@ requires Environment variables for MySQL configuration are defined:
  @   MYSQL_HOST, MYSQL_USER, MYSQL_PASSWORD, MYSQL_DB, MYSQL_PORT != null &&
  @ ensures A single instance of DatabaseManager exists (singleton pattern);
  @ ensures Database connections are established and managed safely;
  @ ensures SQL queries are executed with results fetched or committed to the database;
@*/
"""
class DatabaseManager:
    _instance = None # Singleton Instance

    """
    Description:
    Retrieves the single instance of DatabaseManager. If the instance does not exist, it initializes a new one with
    an optional Flask app for database configuration. This ensures the singleton pattern is maintained.

    Semi-formal Notation:
    /*@ requires app != null on the first call &&
    @ ensures \result == DatabaseManager._instance &&
    @ ensures DatabaseManager._instance != null;
    @*/
    """
    def get_instance(cls, app=None):
        if cls._instance is None:
            cls._instance = cls(app)
        return cls._instance

    """
    Description:
    Initializes the DatabaseManager instance and optionally configures the database using a provided Flask app.
    The instance ensures environment variables are loaded and prepares the manager for database connections.

    Semi-formal Notation:
    /*@ requires os.getenv('MYSQL_HOST') != null &&
    @ requires \forall var \in {MYSQL_USER, MYSQL_PASSWORD, MYSQL_DB, MYSQL_PORT} (os.getenv(var) != null);
    @ ensures self.connection == None &&
    @ ensures app.config is set with MySQL connection details if app != null;
    @*/
    """
    def __init__(self, app=None):
        if DatabaseManager._instance is not None:
            return DatabaseManager._instance
        
        # Load environment variables
        load_dotenv()

        if app:
            self.configure_database(app)
        self.connection = None

    """
    Description:
    Configures the Flask app with MySQL database connection details from environment variables. The app is prepared
    to interact with the database using the configured parameters.

    Semi-formal Notation:
    /*@ requires app != null &&
    @ \forall var \in {MYSQL_HOST, MYSQL_USER, MYSQL_PASSWORD, MYSQL_DB, MYSQL_PORT} (os.getenv(var) != null);
    @ ensures app.config['MYSQL_HOST'] == os.getenv('MYSQL_HOST') &&
    @ ensures app.config['MYSQL_USER'] == os.getenv('MYSQL_USER') &&
    @ ensures app.config['MYSQL_PASSWORD'] == os.getenv('MYSQL_PASSWORD') &&
    @ ensures app.config['MYSQL_DB'] == os.getenv('MYSQL_DB') &&
    @ ensures app.config['MYSQL_PORT'] == int(os.getenv('MYSQL_PORT'));
    @*/
    """
    def configure_database(self, app):
        app.config['MYSQL_HOST'] = os.getenv('MYSQL_HOST')
        app.config['MYSQL_USER'] = os.getenv('MYSQL_USER')
        app.config['MYSQL_PASSWORD'] = os.getenv('MYSQL_PASSWORD')
        app.config['MYSQL_DB'] = os.getenv('MYSQL_DB')
        app.config['MYSQL_PORT'] = int(os.getenv('MYSQL_PORT'))

    """
    Description:
    Establishes a connection to the MySQL database using the configuration details stored in the Flask app.
    This method ensures the connection is ready for executing queries.

    Semi-formal Notation:
    /*@ requires current_app.config['MYSQL_HOST'], current_app.config['MYSQL_USER'],
    @ current_app.config['MYSQL_PASSWORD'], current_app.config['MYSQL_DB'], current_app.config['MYSQL_PORT'] != null;
    @ ensures self.connection != null && self.connection.is_open == True;
    @*/
    """
    def connect(self):
        self.connection = pymysql.connect(
            host=current_app.config['MYSQL_HOST'],
            user=current_app.config['MYSQL_USER'],
            password=current_app.config['MYSQL_PASSWORD'],
            database=current_app.config['MYSQL_DB'],
            port=current_app.config['MYSQL_PORT']
        )

    """
    Description:
    Closes the active database connection, ensuring any open resources are properly cleaned up. If no connection exists,
    the method performs no action.

    Semi-formal Notation:
    /*@ requires self.connection != null &&
    @ ensures self.connection == None &&
    @ ensures No active database connection exists after the method executes;
    @*/
    """
    def close(self):
        if self.connection:
            self.connection.close()
            self.connection = None

    """
    Description:
    Executes a read-only SQL query using the active database connection and fetches the results. The method ensures
    that the query is executed safely with parameters provided, and the connection is closed after use.

    Semi-formal Notation:
    /*@ requires query is a valid SQL SELECT statement &&
    @ requires params matches the placeholders in query &&
    @ self.connection != null after self.connect();
    @ ensures \result == cursor.fetchall() &&
    @ ensures self.connection == None after the method executes;
    @*/
    """
    def execute_query(self, query, params=()):
        self.connect()
        cursor = self.connection.cursor()
        cursor.execute(query, params)
        results = cursor.fetchall()
        cursor.close()
        self.close()
        return results

    """
    Description:
    Executes a SQL query that modifies the database (e.g., INSERT, UPDATE, DELETE) and commits the changes. The method 
    uses a parameterized query to prevent SQL injection, with `params` passed as a tuple of values to bind to the query 
    placeholders. Each element in the tuple corresponds to a placeholder in the query string (e.g., `%s` in MySQL). 
    The connection is closed after the operation.

    Semi-formal Notation:
    /*@ requires query is a valid SQL statement with placeholders (e.g., "INSERT INTO table_name (col1, col2) VALUES (%s, %s)") &&
    @ requires params is a tuple where len(params) matches the number of placeholders in query &&
    @ requires \forall i \in [0, len(params)-1] (params[i] is a valid value for the corresponding SQL column type) &&
    @ self.connection != null after self.connect();
    @ ensures query is executed with the provided parameters (cursor.execute(query, params) == True) &&
    @ ensures changes are committed to the database (self.connection.commit() == True) &&
    @ ensures self.connection == None after the method executes;
    @*/
    """
    def execute_commit(self, query, params=()):
        self.connect()
        cursor = self.connection.cursor()
        cursor.execute(query, params)
        self.connection.commit()
        cursor.close()
        self.close()