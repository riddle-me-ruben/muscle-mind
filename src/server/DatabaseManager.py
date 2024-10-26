# databaseManager.py

import pymysql
from flask import current_app
from dotenv import load_dotenv
import os

class DatabaseManager:
    def __init__(self, app=None):
        # Load environment variables if not already loaded
        load_dotenv()

        if app:
            self.configure_database(app)
        self.connection = None

    def configure_database(self, app):
        """Configures the database settings for a Flask app."""
        app.config['MYSQL_HOST'] = os.getenv('MYSQL_HOST')
        app.config['MYSQL_USER'] = os.getenv('MYSQL_USER')
        app.config['MYSQL_PASSWORD'] = os.getenv('MYSQL_PASSWORD')
        app.config['MYSQL_DB'] = os.getenv('MYSQL_DB')
        app.config['MYSQL_PORT'] = int(os.getenv('MYSQL_PORT'))

    def connect(self):
        """Establish a database connection and store it in self.connection."""
        self.connection = pymysql.connect(
            host=current_app.config['MYSQL_HOST'],
            user=current_app.config['MYSQL_USER'],
            password=current_app.config['MYSQL_PASSWORD'],
            database=current_app.config['MYSQL_DB'],
            port=current_app.config['MYSQL_PORT']
        )
    
    def close(self):
        """Closes the database connection."""
        if self.connection:
            self.connection.close()
            self.connection = None

    def execute_query(self, query, params=()):
        """Executes a SELECT query and returns the results."""
        self.connect()
        cursor = self.connection.cursor()
        cursor.execute(query, params)
        results = cursor.fetchall()
        cursor.close()
        self.close()
        return results

    def execute_commit(self, query, params=()):
        """Executes an INSERT/UPDATE/DELETE query and commits changes."""
        self.connect()
        cursor = self.connection.cursor()
        cursor.execute(query, params)
        self.connection.commit()
        cursor.close()
        self.close()
