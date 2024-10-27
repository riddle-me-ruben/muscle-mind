import pymysql
from flask import current_app
from dotenv import load_dotenv
import os

"""
The DatabaseManager class is responsible for managing connections and executing SQL queries on the MySQL database.
@requires Correct configuration of database credentials and a valid MySQL connection
@ensures Queries are executed safely and connections are managed efficiently for multiple operations
"""
class DatabaseManager:
    """
    Initialize the DatabaseManager and configure the database if the app is provided
    app: Flask - Optional Flask app instance to configure the database
    @requires Environment variables for MySQL database must be set
    @ensures DatabaseManager is ready to connect to the database
    """
    def __init__(self, app=None):
        # Load environment variables
        load_dotenv()

        if app:
            self.configure_database(app)
        self.connection = None

    """
    Configure the database connection details for the app
    app: Flask - The Flask app instance
    @requires Environment variables for MySQL database must be set
    @ensures Flask app config is set with database connection details
    """
    def configure_database(self, app):
        app.config['MYSQL_HOST'] = os.getenv('MYSQL_HOST')
        app.config['MYSQL_USER'] = os.getenv('MYSQL_USER')
        app.config['MYSQL_PASSWORD'] = os.getenv('MYSQL_PASSWORD')
        app.config['MYSQL_DB'] = os.getenv('MYSQL_DB')
        app.config['MYSQL_PORT'] = int(os.getenv('MYSQL_PORT'))

    """
    Establish a connection to the database
    @requires Database configuration to be set up correctly
    @ensures A connection to the MySQL database is established
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
    Close the active database connection if it exists
    @requires An open database connection
    @ensures The database connection is closed
    """
    def close(self):
        if self.connection:
            self.connection.close()
            self.connection = None

    """
    Execute a SQL query and return the result
    query: str - SQL query to execute
    params: tuple - Parameters for the SQL query
    @requires A valid database connection and SQL query
    @ensures SQL query is executed and results are returned
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
    Execute a SQL query with a commit operation
    query: str - SQL query to execute
    params: tuple - Parameters for the SQL query
    @requires A valid database connection and SQL query
    @ensures SQL query is executed and changes are committed to the database
    """
    def execute_commit(self, query, params=()):
        self.connect()
        cursor = self.connection.cursor()
        cursor.execute(query, params)
        self.connection.commit()
        cursor.close()
        self.close()
